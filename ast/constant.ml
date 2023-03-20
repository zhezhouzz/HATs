open Sexplib.Std

type t = U | B of bool | I of int | Prim of string [@@deriving sexp]

let layout = function
  | U -> "()"
  | I i -> string_of_int i
  | B b -> string_of_bool b
  | Prim name -> name
