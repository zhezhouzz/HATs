module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.LRtyRaw
open Sugar
open Aux

let rec pprint_rty rty =
  match rty with
  | BaseRty { cty } -> pprint_parn (To_cty.pprint cty)
  | ArrRty { arr; rethty } -> spf "%s%s" (pprint_arr arr) (pprint_hty rethty)

and pprint_arr = function
  | NormalArr { rx; rty } -> spf "(%s:%s)→" rx (pprint_rty rty)
  | GhostArr { x; ty } -> spf "(%s:%s)⇢" x (Nt.layout ty)
  | ArrArr rty -> spf "%s→" (pprint_rty rty)

and pprint_hty = function
  | Rty rty -> pprint_rty rty
  | Htriple { pre; resrty; post } ->
      spf "[%s]%s[%s]" (To_ltlf.pprint pre) (pprint_rty resrty)
        (To_ltlf.pprint post)
  | Inter (hty1, hty2) -> spf "%s ⊓ %s" (pprint_hty hty1) (pprint_hty hty2)

(* let get_self ct = *)
(*   let open Nt in *)
(*   match ct.rtyp_desc with *)
(*   | Rtyp_extension (name, PTyp ty) -> name.txt #: (Type.core_type_to_t ty) *)
(*   | _ -> *)
(*       let () = Printf.printf "\nct: %s\n" (layout_coretype ct) in *)
(*       _failatwith __FILE__ __LINE__ "" *)

(* let vars_phi_of_ocamlexpr expr = *)
(*   let rec aux expr = *)
(*     match expr.pexp_desc with *)
(*     | Pexp_constraint (e', ct) -> *)
(*         let v = get_self ct in *)
(*         let vs, phi = aux e' in *)
(*         (v :: vs, phi) *)
(*     | _ -> ([], To_qualifier.qualifier_of_ocamlexpr expr) *)
(*   in *)
(*   let vs, prop = aux expr in *)
(*   (List.rev vs, prop) *)

let rec arr_of_ocamlexpr_aux pattern rtyexpr =
  let id = To_pat.patten_to_typed_ids pattern in
  let px =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id
    | _ -> failwith "rty_of_ocamlexpr_aux"
  in
  (* let () = *)
  (*   Printf.printf "get_pat_denoteopt pattern: %s\n" *)
  (*     (match get_pat_denoteopt pattern with None -> "none" | Some x -> x) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "px: %s\n" *)
  (*     (match px with None -> "none" | Some px -> layout_typed (fun x -> x) px) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "rtyexpr: %s\n" *)
  (*     (match rtyexpr with None -> "none" | Some _ -> "some") *)
  (* in *)
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
    (* | Pexp_fun _ -> *)
    (*     _failatwith __FILE__ __LINE__ *)
    (*       (spf "wrong refinement type: %s" *)
    (*          (Pprintast.string_of_expression expr)) *)
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
      let pre, post = map2 To_ltlf.of_ocamlexpr (e1, e3) in
      let resrty = rty_of_ocamlexpr_aux e2 in
      match (id1, id2, id3) with
      | "pre", "res", "post" -> Htriple { pre; resrty; post }
      | "pre", "res", "newadding" ->
          Htriple { pre; resrty; post = SeqL (pre, post) }
      | _ ->
          failwith
            "syntax error: {pre = ...; res = ...; post = ...} or {pre = ...; \
             res = ...; newadding = ...}"
      (* | Pexp_array ls when List.length ls -> *)
      (* failwith "syntax error: empty intersection type" *))
  | Pexp_array ls -> (
      let htys = List.map hty_of_ocamlexpr_aux ls in
      match htys with
      | [] -> failwith "syntax error: empty intersection type"
      | hty :: htys -> List.fold_left (fun h1 h2 -> Inter (h1, h2)) hty htys)
  | _ -> Rty (rty_of_ocamlexpr_aux expr)

let rty_of_ocamlexpr expr =
  let rty = rty_of_ocamlexpr_aux expr in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  rty

let hty_of_ocamlexpr expr =
  let hty = hty_of_ocamlexpr_aux expr in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  hty

let layout_hty = pprint_hty
let layout_rty = pprint_rty
