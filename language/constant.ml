open Sexplib.Std

type t = Unit | Int of int | Prim of string [@@deriving sexp]

let layout = function
  | Unit -> "‹›"
  | Int i -> string_of_int i
  | Prim name -> name
