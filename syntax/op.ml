open Sexplib.Std

type t = DtOp of string | EffOp of string | BuiltinOp of string
[@@deriving sexp]

let compare a b = Sexplib.Sexp.compare (sexp_of_t a) (sexp_of_t b)
let id_eq_op = function BuiltinOp "==" -> true | _ -> false
let id_is_dt name = String.(equal name @@ capitalize_ascii name)
let to_string = function DtOp op -> op | EffOp op -> op | BuiltinOp op -> op
let mk_eq_op = BuiltinOp "=="

let force_id_to_op str =
  match str with
  | "mod" -> BuiltinOp str
  | _ ->
      let str' = String.capitalize_ascii str in
      if String.equal str str' then BuiltinOp str else EffOp str'

let eq a b =
  let aux = function
    | DtOp a, DtOp b -> String.equal a b
    | EffOp a, EffOp b -> String.equal a b
    | BuiltinOp a, BuiltinOp b -> String.equal a b
    | _, _ -> false
  in
  let res = aux (a, b) in
  (* let () = *)
  (*   Printf.printf "%s =? %s : %b\n" *)
  (*     (Sexplib.Sexp.to_string @@ sexp_of_t a) *)
  (*     (Sexplib.Sexp.to_string @@ sexp_of_t b) *)
  (*     res *)
  (* in *)
  res
