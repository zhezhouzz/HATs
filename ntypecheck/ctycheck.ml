open Language
module Typectx = NTypectx

(* open Zzdatatype.Datatype *)
open Qualifiercheck
open RtyRaw.Cty
(* open Aux *)

let check opctx ctx { v; phi } =
  let ctx' = Typectx.new_to_rights ctx [ v ] in
  let phi = type_check_qualifier opctx ctx' phi in
  { v; phi }
