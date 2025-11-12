open Ppxlib

val replace_variable
  :  f:(label loc -> [ `Remove | `Rename of label ])
  -> pattern
  -> pattern

val pattern_variables : pattern -> (pattern * label loc) list

(** Bind each non-wildcard variable of each pattern to the expression which projects the
    bound expression to the variable's component. *)
val project_pattern_variables
  :  assume_exhaustive:bool
  -> modul:longident loc option
  -> with_location:Ppx_let_expander.With_location.t
  -> value_binding list
  -> value_binding loc list

(** Suppresses unused var warnings for variables definitely used in the when clause, even
    when the when clause is removed. *)
val add_usages_for_vars_definitely_used_in_when_clause : case -> case

(** Produces a match-like expression which first matches on the index of the inhabited
    case, and then on the case itself. [switch] is used to create a match-like statement,
    and [destruct] is used to bind each of the variables in the case patterns so that they
    are available in the case bodies *)
val indexed_match
  :  loc:location
  -> modul:longident loc option
  -> destruct:
       (assume_exhaustive:bool
        -> loc:location
        -> modul:longident loc option
        -> lhs:pattern
        -> rhs:expression
        -> body:expression
        -> expression option)
  -> switch:
       (loc:location
        -> switch_loc:location
        -> modul:longident loc option
        -> expression
        -> case list
        -> expression)
  -> expression
  -> case list
  -> expression

type t

val bind : t
val map : t
val expand : t -> modul:longident loc option -> loc:location -> expression -> expression
