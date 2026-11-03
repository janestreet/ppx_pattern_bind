open Ppx_helpers.Base_lite
open Ppxlib
open Ast_builder.Default
open Ppx_let_expander

let locality = Locality.global

let pexp_let ~loc rec_ bindings e =
  match bindings with
  | [] -> e
  | _ :: _ -> pexp_let ~loc rec_ bindings e
;;

let rec swap_constrained_alias_with_constrained_var_if_needed (pattern : pattern) =
  match Ppxlib_jane.Shim.Pattern_desc.of_parsetree pattern.ppat_desc with
  | Ppat_alias (_, var) | Ppat_var var ->
    Some (ppat_var ~loc:{ pattern.ppat_loc with loc_ghost = true } var, var)
  | Ppat_constraint (inner, Some t, _) ->
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
  List.sort_uniq
    ~cmp:(fun (_, x) (_, y) -> String.compare x.txt y.txt)
    (variables_of#pattern pattern [])
;;

let rec remove_constraint_from_var_or_alias pattern =
  match Ppxlib_jane.Shim.Pattern_desc.of_parsetree pattern.ppat_desc with
  | Ppat_constraint (({ ppat_desc = Ppat_var _ | Ppat_alias _; _ } as inner), _, _) ->
    Some inner
  | Ppat_constraint (inner, _, _) ->
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
    match Ppxlib_jane.Shim.Pattern_desc.of_parsetree pattern.ppat_desc with
    | Ppat_var var | Ppat_alias (_, var) -> Some (pattern, var)
    | Ppat_constraint (inner, _, _) -> helper inner
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

let warning_attribute ~loc str =
  attribute
    ~loc
    ~name:(Loc.make ~loc "ocaml.warning")
    ~payload:(PStr [ pstr_eval ~loc (estring ~loc str) [] ])
;;

let with_warning_attribute str expr =
  let loc = expr.pexp_loc in
  { expr with pexp_attributes = warning_attribute ~loc str :: expr.pexp_attributes }
;;

let case_number ~loc ~modul exp ~reachable_cases ~unreachable_cases =
  with_warning_attribute
    "-26-27" (* unused variable warnings *)
    (expand_match
       Ppx_let_expander.map
       ~extension_kind:Extension_kind.default
       ~loc
       ~modul
       ~locality
       exp
       (List.mapi reachable_cases ~f:(fun idx case ->
          { case with pc_rhs = eint ~loc idx })
        @ unreachable_cases))
;;

let estimate_variables_used_in expr variables =
  let vars_used = String.Table.create () in
  let find_vars =
    object
      inherit Ast_traverse.iter as super

      method! expression_desc desc =
        match desc with
        | Pexp_ident { txt = Lident v; loc } ->
          if String.Set.mem variables v
          then String.Table.add_exn vars_used ~key:v ~data:loc
        (* We just stop descending here since we don't know if someone is shadowing a
           variable. If there's demand, we can implement most of the cases here, but
           hopefully, nobody is using these in their when clauses. *)
        | Pexp_let _
        | Pexp_function _
        | Pexp_match _
        | Pexp_try _
        | Pexp_for _
        | Pexp_object _
        | Pexp_open _
        | Pexp_letop _ -> ()
        | _ -> super#expression_desc desc
    end
  in
  find_vars#expression expr;
  String.Table.to_alist vars_used
  |> List.sort ~compare:(fun (var1, _) (var2, _) -> String.compare var1 var2)
  |> List.map ~f:(fun (txt, loc) -> { txt; loc })
;;

let add_dummy_usages expr = function
  | [] -> expr
  | _ :: _ as usages ->
    let value_bindings =
      List.map usages ~f:(fun { txt = var; loc } ->
        let loc = { loc with loc_ghost = true } in
        value_binding
          ~loc
          ~pat:[%pat? (_ : _)]
          ~expr:(Ast_helper.Exp.ident ~loc { loc; txt = Lident var }))
    in
    pexp_let ~loc:{ expr.pexp_loc with loc_ghost = true } Nonrecursive value_bindings expr
;;

let add_usages_for_vars_definitely_used_in_when_clause case =
  match case.pc_guard with
  | None -> case
  | Some guard ->
    let lhs_vars =
      pattern_variables case.pc_lhs
      |> List.map ~f:(fun (_, l) -> l.txt)
      |> String.Set.of_list
    in
    let vars_used_in_guard = estimate_variables_used_in guard lhs_vars in
    { case with pc_rhs = add_dummy_usages case.pc_rhs vars_used_in_guard }
;;

let expand_case ~destruct expr idx match_case =
  let match_case = add_usages_for_vars_definitely_used_in_when_clause match_case in
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

let case_number_cases ~loc ~destruct exp reachable_cases =
  List.mapi reachable_cases ~f:(expand_case ~destruct exp) @ [ catch_all_case ~loc ]
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
  let unreachable_cases, reachable_cases =
    List.partition cases ~f:(fun case ->
      match case.pc_rhs.pexp_desc with
      | Pexp_unreachable -> true
      | _ -> false)
  in
  let hider =
    object
      inherit Ast_traverse.map as super
      method! location loc = super#location { loc with loc_ghost = true }
    end
  in
  let case_number =
    hider#expression
      (constraint_remover#expression
         (case_number ~loc ~modul expr ~reachable_cases ~unreachable_cases))
  in
  let assume_exhaustive = List.length cases <= 1 in
  let destruct = destruct ~assume_exhaustive ~loc ~modul in
  let case_number_cases = case_number_cases ~loc ~destruct expr reachable_cases in
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
    then pexp_function_cases ~loc [ project_the_var ]
    else
      with_warning_attribute
        "-11" (* unused case warning *)
        (pexp_function_cases ~loc [ project_the_var; catch_all_case ~loc ])
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
