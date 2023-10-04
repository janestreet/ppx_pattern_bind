open Base
open Ppxlib
open Ast_builder.Default
open Ppx_let_expander

let locality = `global

let pexp_let ~loc rec_ bindings e =
  match bindings with
  | [] -> e
  | _ :: _ -> pexp_let ~loc rec_ bindings e
;;

let rec swap_constrained_alias_with_constrained_var_if_needed (pattern : pattern) =
  match pattern.ppat_desc with
  | Ppat_alias (_, var) | Ppat_var var ->
    Some (ppat_var ~loc:{ pattern.ppat_loc with loc_ghost = true } var, var)
  | Ppat_constraint (inner, t) ->
    (match swap_constrained_alias_with_constrained_var_if_needed inner with
     | Some (inner, var) ->
       Some (ppat_constraint ~loc:{ inner.ppat_loc with loc_ghost = true } inner t, var)
     | None -> None)
  | _ -> None
;;

let variables_of =
  object
    inherit [(pattern * string loc) list] Ast_traverse.fold as super

    method! pattern p acc =
      let acc =
        match p.ppat_desc with
        | Ppat_var var -> (p, var) :: acc
        | Ppat_alias (_, var) -> (ppat_var ~loc:var.loc var, var) :: acc
        | Ppat_constraint _ ->
          (match swap_constrained_alias_with_constrained_var_if_needed p with
           | None -> acc
           | Some (p, var) -> (p, var) :: acc)
        | _ -> acc
      in
      super#pattern p acc
  end
;;

let pattern_variables pattern =
  List.dedup_and_sort
    ~compare:(fun (_, x) (_, y) -> String.compare x.txt y.txt)
    (variables_of#pattern pattern [])
;;

let rec remove_constraint_from_var_or_alias pattern =
  match pattern.ppat_desc with
  | Ppat_constraint (({ ppat_desc = Ppat_var _ | Ppat_alias _; _ } as inner), _) ->
    Some inner
  | Ppat_constraint (inner, _) ->
    (match remove_constraint_from_var_or_alias inner with
     | Some inner -> Some inner
     | None -> None)
  | _ -> None
;;

let constraint_remover =
  object
    inherit Ast_traverse.map as super

    method! pattern pattern =
      let pattern =
        match remove_constraint_from_var_or_alias pattern with
        | Some pattern -> pattern
        | None -> pattern
      in
      super#pattern pattern
  end
;;

let catch_all_case ~loc =
  case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:(pexp_assert ~loc (ebool ~loc false))
;;

type pat_exh =
  { pat : pattern
  ; assume_exhaustive : bool
  }

let extract_var_or_alias_pattern (pattern : pattern) ~f =
  let rec helper pattern =
    match pattern.ppat_desc with
    | Ppat_var var | Ppat_alias (_, var) -> Some (pattern, var)
    | Ppat_constraint (inner, _) -> helper inner
    | _ -> None
  in
  match helper pattern with
  | Some (inner, x) ->
    (match f x with
     | `Rename _ -> pattern
     | `Remove -> inner)
  | None -> pattern
;;

let replace_variable ~f x =
  let replacer =
    object
      inherit Ast_traverse.map as super

      method! pattern p =
        let p = extract_var_or_alias_pattern p ~f in
        let p = super#pattern p in
        let loc = { p.ppat_loc with loc_ghost = true } in
        match p.ppat_desc with
        | Ppat_var v ->
          (match f v with
           | `Rename tmpvar -> ppat_var ~loc { txt = tmpvar; loc = v.loc }
           | `Remove -> ppat_any ~loc)
        | Ppat_alias (sub, v) ->
          (match f v with
           | `Rename tmpvar -> ppat_alias ~loc sub { txt = tmpvar; loc = v.loc }
           | `Remove -> sub)
        | _ -> p
    end
  in
  replacer#pattern x
;;

let with_warning_attribute str expr =
  let loc = expr.pexp_loc in
  { expr with
    pexp_attributes =
      attribute
        ~loc
        ~name:(Loc.make ~loc "ocaml.warning")
        ~payload:(PStr [ pstr_eval ~loc (estring ~loc str) [] ])
      :: expr.pexp_attributes
  }
;;

let case_number ~loc ~modul exp indexed_cases =
  with_warning_attribute
    "-26-27" (* unused variable warnings *)
    (expand_match
       Ppx_let_expander.map
       ~extension_kind:Extension_kind.default
       ~loc
       ~modul
       ~locality
       exp
       (List.map indexed_cases ~f:(fun (idx, case) ->
          { case with pc_rhs = eint ~loc idx })))
;;

let expand_case ~destruct expr (idx, match_case) =
  let rhs =
    let loc = expr.pexp_loc in
    destruct ~lhs:match_case.pc_lhs ~rhs:expr ~body:match_case.pc_rhs
    |> Option.value
         ~default:
           (pexp_let
              ~loc
              Nonrecursive
              [ value_binding ~loc ~pat:match_case.pc_lhs ~expr ]
              (Merlin_helpers.focus_expression match_case.pc_rhs))
  in
  case
    ~lhs:(Merlin_helpers.hide_pattern (pint ~loc:match_case.pc_lhs.ppat_loc idx))
    ~guard:None
    ~rhs
;;

let case_number_cases ~loc ~destruct exp indexed_cases =
  List.map indexed_cases ~f:(expand_case ~destruct exp) @ [ catch_all_case ~loc ]
;;

let name_expr expr =
  (* to avoid duplicating non-value expressions *)
  match expr.pexp_desc with
  | Pexp_ident _ -> [], expr
  | _ ->
    let loc = { expr.pexp_loc with loc_ghost = true } in
    let var = gen_symbol ~prefix:"__pattern_syntax" () in
    [ do_not_enter_value (value_binding ~loc ~pat:(pvar ~loc var) ~expr) ], evar ~loc var
;;

let indexed_match ~loc ~modul ~destruct ~switch expr cases =
  let first_case = List.hd_exn cases in
  let first_case_loc = first_case.pc_lhs.ppat_loc in
  let switch_loc =
    { loc_ghost = true; loc_start = first_case_loc.loc_start; loc_end = loc.loc_end }
  in
  let expr_binding, expr = name_expr expr in
  let indexed_cases = List.mapi cases ~f:(fun idx case -> idx, case) in
  let hider =
    object
      inherit Ast_traverse.map as super
      method! location loc = super#location { loc with loc_ghost = true }
    end
  in
  let case_number =
    hider#expression
      (constraint_remover#expression (case_number ~loc ~modul expr indexed_cases))
  in
  let assume_exhaustive = List.length cases <= 1 in
  let destruct = destruct ~assume_exhaustive ~loc ~modul in
  let case_number_cases = case_number_cases ~loc ~destruct expr indexed_cases in
  pexp_let
    ~loc
    Nonrecursive
    expr_binding
    (switch ~loc ~switch_loc ~modul case_number case_number_cases)
;;

let project_bound_var ~loc ~modul ~with_location exp ~pat:{ pat; assume_exhaustive } var =
  let project_the_var =
    (* We use a fresh var name because the compiler conflates all definitions with the
       name * location, for the purpose of emitting warnings. *)
    let tmpvar = gen_symbol ~prefix:"__pattern_syntax" () in
    let pattern =
      replace_variable pat ~f:(fun v ->
        if String.equal v.txt var.txt then `Rename tmpvar else `Remove)
    in
    case
      ~lhs:{ pattern with ppat_loc = { pattern.ppat_loc with loc_ghost = true } }
      ~guard:None
      ~rhs:(evar ~loc tmpvar)
  in
  let fn =
    if assume_exhaustive
    then pexp_function ~loc [ project_the_var ]
    else
      with_warning_attribute
        "-11" (* unused case warning *)
        (pexp_function ~loc [ project_the_var; catch_all_case ~loc ])
  in
  let fn = constraint_remover#expression fn in
  bind_apply
    ~prevent_tail_call:false
    ~op_name:Map.name
    ~loc
    ~modul
    ~with_location
    ~arg:exp
    ~fn
;;

let project_bound_vars ~loc ~modul ~with_location exp ~lhs =
  let loc = { loc with loc_ghost = true } in
  let variables = pattern_variables lhs.pat in
  List.map variables ~f:(fun (_, var) ->
    { txt =
        (let expr = project_bound_var ~loc ~modul ~with_location exp ~pat:lhs var () in
         value_binding
           ~loc
           ~pat:(ppat_var ~loc:var.loc var)
           ~expr:(Merlin_helpers.hide_expression expr))
    ; loc
    })
;;

let project_pattern_variables ~assume_exhaustive ~modul ~with_location vbs =
  List.concat_map vbs ~f:(fun vb ->
    let loc = { vb.pvb_loc with loc_ghost = true } in
    project_bound_vars
      ~loc
      ~modul
      ~with_location
      vb.pvb_expr
      ~lhs:{ pat = vb.pvb_pat; assume_exhaustive })
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
    -> switch_loc:location
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
    [ do_not_enter_value (value_binding ~loc ~pat:(pvar ~loc var) ~expr) ], evar ~loc var
;;

let switch ~loc ~switch_loc:_ ~modul value cases =
  Ppx_let_expander.expand
    Ppx_let_expander.bind
    Ppx_let_expander.Extension_kind.default
    ~modul
    ~locality
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
        ~locality
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
  |> project_pattern_variables ~assume_exhaustive ~modul ~with_location:false
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
  indexed_match ~loc ~modul ~destruct ~switch:Ext.switch expr cases
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
