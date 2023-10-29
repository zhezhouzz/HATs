module MetaEnv = Env
open Ocaml5_parser
open Parsetree

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

(* let hty_of_ocamlexpr expr = *)
(*   let ltlf_hty = To_ltlf_hty.hty_of_ocamlexpr expr in *)
(*   let hty = to_hty ltlf_hty in *)
(*   let hty = normalize_name_hty hty in *)
(*   hty *)

(* let rty_of_ocamlexpr expr = *)
(*   let ltlf_rty = To_ltlf_hty.rty_of_ocamlexpr expr in *)
(*   let rty = to_rty ltlf_rty in *)
(*   let rty = normalize_name_rty rty in *)
(*   rty *)

(* let hty_of_ocamlexpr expr = *)
(*   let ltlf_hty = To_ltlf_hty.hty_of_ocamlexpr expr in *)
(*   let hty = to_hty ltlf_hty in *)
(*   let hty = normalize_name_hty hty in *)
(*   hty *)

(* let rty_of_ocamlexpr expr = *)
(*   let ltlf_rty = To_ltlf_hty.rty_of_ocamlexpr expr in *)
(*   let rty = to_rty ltlf_rty in *)
(*   let rty = normalize_name_rty rty in *)
(*   rty *)

let rec arr_of_ocamlexpr_aux pattern rtyexpr =
  let id = To_pat.patten_to_typed_ids pattern in
  let px =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id
    | _ -> failwith "rty_of_ocamlexpr_aux"
  in
  match (get_pat_denoteopt pattern, px, rtyexpr) with
  | None, None, Some rtyexpr -> ArrArr (rty_of_ocamlexpr_aux rtyexpr)
  | None, Some { x = rx; _ }, Some rtyexpr ->
      NormalArr { rx; rty = rty_of_ocamlexpr_aux rtyexpr }
  | Some "ghost", Some { x; ty = Some ty' }, None -> GhostArr Nt.{ x; ty = ty' }
  | _, _, _ -> _failatwith __FILE__ __LINE__ "wrong syntax"

and rty_of_ocamlexpr_aux expr =
  let aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> BaseRty { cty = To_cty.of_ocamlexpr expr }
    | Pexp_fun (_, rtyexpr, pattern, body) ->
        let arr = arr_of_ocamlexpr_aux pattern rtyexpr in
        ArrRty { arr; rethty = hty_of_ocamlexpr_aux body }
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

and hty_of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  | Pexp_record ([ (id1, e1); (id2, e2); (id3, e3) ], None) -> (
      let id1, id2, id3 = map3 To_id.longid_to_id (id1, id2, id3) in
      let pre, post = map2 To_srl.of_ocamlexpr (e1, e3) in
      let resrty = rty_of_ocamlexpr_aux e2 in
      match (id1, id2, id3) with
      | "pre", "res", "post" -> Htriple { pre; resrty; post }
      | "pre", "res", "newadding" ->
          Htriple { pre; resrty; post = SeqA (pre, post) }
      | _ ->
          failwith
            "syntax error: {pre = ...; res = ...; post = ...} or {pre = ...; \
             res = ...; newadding = ...}"
      (* | Pexp_array ls when List.length ls -> *)
      (* failwith "syntax error: empty intersection type" *))
  | Pexp_record (_, _) ->
      failwith
        (spf "syntax error: Hoare Automata Triple %s\n"
           (Pprintast.string_of_expression expr))
  | Pexp_array ls -> (
      let htys = List.map hty_of_ocamlexpr_aux ls in
      match htys with
      | [] -> failwith "syntax error: empty intersection type"
      | hty :: htys -> List.fold_left (fun h1 h2 -> Inter (h1, h2)) hty htys)
  | _ -> Rty (rty_of_ocamlexpr_aux expr)

let rty_of_ocamlexpr expr =
  let rty = rty_of_ocamlexpr_aux expr in
  let rty = normalize_name_rty rty in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  rty

let hty_of_ocamlexpr expr =
  let hty = hty_of_ocamlexpr_aux expr in
  let hty = normalize_name_hty hty in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  hty

let layout_hty = pprint_hty
let layout_rty = pprint_rty
