open Base
open Ppxlib
open Ast_builder.Default

let pexp_let ~loc rec_ bindings e =
  match bindings with
  | [] -> e
  | _ :: _ -> pexp_let ~loc rec_ bindings e
;;

module type Ext = sig
  (* The part that goes after [let%] and [match%]. If the name is
     "pattern_bind", then [let%pattern_bind] and [match%pattern_bind] are
     what get expanded. *)
  val name : string

  (* Given a list of variables bound to their corresponding "projection expression" (the
     expression that maps the original expression to the variable's component),
     [bind_pattern_projections] returns [rhs], possibly as the body of a [let] expression
     bringing the input variables in scope. *)
  val bind_pattern_projections
    :  loc:location
    -> modul:longident loc option
    -> value_binding list
    -> rhs:expression
    -> expression

  (* Produces a match-like expression (indeed, it could just be a [match] expression).
     This function is not expected to destructure or transform the list of cases. *)
  val switch
    :  loc:location
    -> modul:longident loc option
    -> expression
    -> case list
    -> expression
end

type t = (module Ext)

let gen_symbol_prefix = "__pattern_syntax"

let name_expr expr =
  (* to avoid duplicating non-value expressions *)
  match expr.pexp_desc with
  | Pexp_ident _ -> [], expr
  | _ ->
    let loc = { expr.pexp_loc with loc_ghost = true } in
    let var = gen_symbol ~prefix:gen_symbol_prefix () in
    [ value_binding ~loc ~pat:(pvar ~loc var) ~expr ], evar ~loc var
;;

let switch ~loc ~modul value cases =
  Ppx_let_expander.expand
    Ppx_let_expander.bind
    Ppx_let_expander.Extension_kind.default
    ~modul
    (Merlin_helpers.hide_expression (pexp_match ~loc value cases))
;;

module Bind : Ext = struct
  let name = "pattern_bind"

  let bind_pattern_projections ~loc ~modul:_ projection_bindings ~rhs =
    let loc = { loc with loc_ghost = true } in
    (* For [let%pattern_bind], we don't bind on the match case, so nothing
       constrains the resulting expression to be an incremental. We used to
       generate [if false then return (assert false) else <expr>] to
       compensate, but that causes problems with the defunctorized interface
       of incremental, as [return] takes an extra argument. [if false then
       map (assert false) ~f:Fn.id else <expr>] avoids that but causes type
       errors in bonsai where they sort of abuse this preprocessor by using
       this with this thing that's not a monad (see legacy_api.ml). *)
    pexp_let ~loc Nonrecursive projection_bindings rhs
  ;;

  let switch = switch
end

module Map : Ext = struct
  let name = "pattern_map"

  let bind_pattern_projections ~loc ~modul projection_bindings ~rhs =
    let loc = { loc with loc_ghost = true } in
    let let_ = pexp_let ~loc Nonrecursive projection_bindings rhs in
    match projection_bindings with
    | [] -> Ppx_let_expander.qualified_return ~loc ~modul rhs
    | _ :: _ ->
      Ppx_let_expander.expand
        Ppx_let_expander.map
        Ppx_let_expander.Extension_kind.default
        ~modul
        let_
  ;;

  let switch = switch
end

let bind = (module Bind : Ext)
let map = (module Map : Ext)

let error_if_invalid_pattern (module Ext : Ext) pattern =
  let finder =
    object
      inherit Ast_traverse.iter as super

      method! pattern p =
        super#pattern p;
        match p.ppat_desc with
        | Ppat_unpack _ ->
          Location.raise_errorf
            ~loc:p.ppat_loc
            "%%%s cannot be used with (module ..) patterns."
            Ext.name
        | Ppat_exception _ ->
          Location.raise_errorf
            ~loc:p.ppat_loc
            "%%%s cannot be used with exception patterns."
            Ext.name
        | _ -> ()
    end
  in
  finder#pattern pattern
;;

(* Translations for let%pattern_bind

   let%pattern_bind (x, y, _) = e1
   and { z; _} = e2
   in exp

   ===>

   let v1 = e1
   and v2 = e2
   in
   let x = let%map (x, _, _) = v1 in x
   and y = let%map (_, y, _) = v1 in y
   and z = let%map { z; _} = v2 in z
   in
   exp
*)

let save_rhs_of_bindings vbs =
  let save_bindings, vbs =
    List.unzip
      (List.map vbs ~f:(fun vb ->
         let b, expr = name_expr vb.pvb_expr in
         b, { vb with pvb_expr = expr }))
  in
  List.concat save_bindings, vbs
;;

let expand_let (module Ext : Ext) ~assume_exhaustive ~loc ~modul vbs rhs =
  List.iter vbs ~f:(fun vb -> error_if_invalid_pattern (module Ext) vb.pvb_pat);
  let save_bindings, vbs = save_rhs_of_bindings vbs in
  vbs
  |> Ppx_let_expander.project_pattern_variables
       ~assume_exhaustive
       ~modul
       ~with_location:false
  |> List.map ~f:Loc.txt
  |> Ext.bind_pattern_projections ~loc ~modul ~rhs
  |> pexp_let Nonrecursive ~loc save_bindings
;;

(* Translations for match%pattern_bind


   {[
     match%pattern_bind e with
     | A x -> render_a x
     | B (y, z) -> render_b (y, z)
   ]}

   ===>

   {[
     let exp = e in
     match%bind
       match%map exp with
       | A _ -> 0
       | B (_, _) -> 1
     with
     | 0 ->
       let x =
         match%map exp with
         | A x -> x
         | _ -> assert false
       in
       render_a x
     | 1 ->
       let y =
         match%map exp with
         | B (y, _) -> y
         | _ -> assert false
       and z =
         match%map exp with
         | B (_, z) -> z
         | _ -> assert false
       in
       render_b (y, z)
     | _ -> assert false
   ]}

   and match%pattern_map is the same thing where the inner [lets] like
   [let y = .. and z = ..] are let%map.
*)

let expand_match ~modul (module Ext : Ext) ~loc expr cases =
  let loc = { loc with loc_ghost = true } in
  List.iter cases ~f:(fun { pc_lhs; pc_guard; _ } ->
    error_if_invalid_pattern (module Ext) pc_lhs;
    match pc_guard with
    | None -> ()
    | Some v ->
      (* We tried to support this, but ending up reverting (in 189712731a6): it seems
         hard/impossible to have the desired warning and performance. *)
      Location.raise_errorf ~loc:v.pexp_loc "%%%s cannot be used with `when`." Ext.name);
  let destruct ~assume_exhaustive ~loc ~modul ~lhs ~rhs ~body =
    let bindings = [ value_binding ~loc ~pat:lhs ~expr:rhs ] in
    Some (expand_let (module Ext) ~assume_exhaustive ~loc ~modul bindings body)
  in
  Ppx_let_expander.indexed_match ~loc ~modul ~destruct ~switch:Ext.switch expr cases
;;

let expand (module Ext : Ext) ~modul ~loc expr =
  match expr.pexp_desc with
  | Pexp_let (rec_flag, vbs, exp) ->
    (match rec_flag with
     | Nonrecursive -> ()
     | Recursive ->
       Location.raise_errorf ~loc "%%%s cannot be used with 'let rec'" Ext.name);
    expand_let (module Ext) ~assume_exhaustive:true ~loc ~modul vbs exp
  | Pexp_match (expr, cases) -> expand_match (module Ext) ~loc ~modul expr cases
  | _ ->
    Location.raise_errorf ~loc "'%%%s can only be used with 'let' and 'match'" Ext.name
;;

let extension (module Ext : Ext) =
  Extension.declare_with_path_arg
    Ext.name
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    (fun ~loc ~path:_ ~arg expr -> expand (module Ext) ~modul:arg ~loc expr)
;;

let () =
  Driver.register_transformation "pattern" ~extensions:[ extension bind; extension map ]
;;
