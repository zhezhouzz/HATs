open Sexplib.Std

type t = U | B of bool | I of int | Tu of t list | Dt of string * t list
[@@deriving sexp]

open Zzdatatype.Datatype
open Sugar

let rec layout = function
  | U -> "()"
  | I i -> string_of_int i
  | B b -> string_of_bool b
  | Tu vs -> spf "(%s)" (List.split_by_comma layout vs)
  | Dt (op, vs) -> spf "%s (%s)" op (List.split_by_comma layout vs)

let is_bool_opt = function B b -> Some b | _ -> None
let is_dt_opt = function Dt (op, vs) -> Some (op, vs) | _ -> None
let mk_dt op vs = Dt (op, vs)

let rec infer_const_ty = function
  | U -> Nt.unit_ty
  | I _ -> Nt.int_ty
  | B _ -> Nt.bool_ty
  | Tu vs -> Nt.mk_tuple (List.map infer_const_ty vs)
  | Dt (_, _) -> _failatwith __FILE__ __LINE__ "no dt const"
