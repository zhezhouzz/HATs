open Sexplib.Std

type t = Unit | Int of int | Prim of string [@@deriving sexp]
