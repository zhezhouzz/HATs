open Sexplib.Std

type t = DtOp of string | EffOp of string | BuiltinOp of string
[@@deriving sexp]

let compare a b = Sexplib.Sexp.compare (sexp_of_t a) (sexp_of_t b)
let id_is_dt name = String.(equal name @@ capitalize_ascii name)
let to_string = function DtOp op -> op | EffOp op -> op | BuiltinOp op -> op

let eq a b =
  let aux = function
    | DtOp a, DtOp b -> String.equal a b
    | EffOp a, EffOp b -> String.equal a b
    | BuiltinOp a, BuiltinOp b -> String.equal a b
    | _, _ -> false
  in
  aux (a, b)