open Sexplib.Std

type t = U | B of bool | I of int | Tu of t list | Dt of Pmop.t * t list
[@@deriving sexp]

open Zzdatatype.Datatype
open Sugar

let rec layout = function
  | U -> "()"
  | I i -> string_of_int i
  | B b -> string_of_bool b
  | Tu vs -> spf "(%s)" (List.split_by_comma layout vs)
  | Dt (op, vs) ->
      spf "%s (%s)" (Pmop.t_to_string op) (List.split_by_comma layout vs)

let is_bool_opt = function B b -> Some b | _ -> None
let is_dt_opt = function Dt (op, vs) -> Some (op, vs) | _ -> None
let mk_dt op vs = Dt (op, vs)
