module Nctx = Languages.UTSimpleTypectx
module Typectx = Languages.MustMayTypectx
(* open Abstraction *)

(* type rec_info = { fix_name : string; rank_lhs : string } *)

type uctx = {
  (* rec_info : rec_info option; *)
  ctx : Typectx.ctx;
  nctx : Typectx.ctx;
  libctx : Nctx.ctx;
}

exception FailwithCex of string * Z3.Model.model
exception FailTimeout of string * int
exception FailUnderAgainstOver of string * int
exception FailOverAgainstUnder of string * int
exception FailTypeConsumedonsumed of string * int * string

let _err_consumed file line name =
  raise (FailTypeConsumedonsumed (file, line, name))
