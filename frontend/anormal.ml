module T = Ast.Termlang
module StrucNA = Ast.StrucNA
module Struc = Ast.Struc

let layout to_term code =
  let open Ast.NL in
  let _, code = fix_to_lam code in
  Expr.layout @@ to_term code

open Sugar
open Zzdatatype.Datatype

let layout_one to_term StrucNA.{ name; body } =
  let open Ast.NL in
  let if_rec, body = fix_to_lam body in
  let body = to_term body in
  Structure.layout_one Struc.{ if_rec; name; body }

let struct_layout to_term code =
  spf "%s\n" (List.split_by "\n" (layout_one to_term) code)
