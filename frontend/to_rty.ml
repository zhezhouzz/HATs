module MetaEnv = Env
(* open Ocaml5_parser *)

(* open Parsetree *)
(* open Zzdatatype.Datatype *)
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar
open Aux

let rec pprint_rty rty =
  match rty with
  | BaseRty { cty } -> pprint_parn (To_cty.pprint cty)
  | ArrRty { arr; rethty } -> spf "%s%s" (pprint_arr arr) (pprint_hty rethty)

and pprint_arr = function
  | NormalArr { rx; rty } -> spf "(%s:%s) → " rx (pprint_rty rty)
  | GhostArr { x; ty } -> spf "(%s:%s) ⇢ " x (Nt.layout ty)
  | ArrArr rty -> spf "%s → " (pprint_rty rty)

and pprint_hty = function
  | Rty rty -> pprint_rty rty
  | Htriple { pre; resrty; post } ->
      spf "[%s]%s[%s]" (To_srl.pprint pre) (pprint_rty resrty)
        (To_srl.pprint post)
  | Inter (hty1, hty2) -> spf "%s ⊓ %s" (pprint_hty hty1) (pprint_hty hty2)

let hty_of_ocamlexpr expr =
  let ltlf_hty = To_ltlf_hty.hty_of_ocamlexpr expr in
  let hty = to_hty ltlf_hty in
  let hty = normalize_name_hty hty in
  hty

let rty_of_ocamlexpr expr =
  let ltlf_rty = To_ltlf_hty.rty_of_ocamlexpr expr in
  let rty = to_rty ltlf_rty in
  let rty = normalize_name_rty rty in
  rty

let layout_hty = pprint_hty
let layout_rty = pprint_rty
