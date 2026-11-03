open Ppxlib

type t

val bind : t
val map : t
val expand : t -> modul:longident loc option -> loc:location -> expression -> expression
