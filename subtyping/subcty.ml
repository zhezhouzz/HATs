open Language
module Rty = Language.Rty
open Rty
open Zzdatatype.Datatype
open Sugar
(* open Auxtyping *)

let close_rtyped_to_prop x prop =
  (* let open P in *)
  let x, phix = cty_typed_to_prop x in
  smart_pi (x, phix) prop

let close_rtypeds_to_prop l prop = List.fold_right close_rtyped_to_prop l prop

let layout_qv { cx; cty } =
  if Cty.is_true cty.phi then spf "%s:%s" cx @@ layout cty.v.ty
  else spf "%s:{%s}" cx @@ layout_cty cty

let aux_sub_cty uqvs { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  (* let open P in *)
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "uqvs: %s\n" @@ List.split_by_comma layout_qv uqvs
  in
  let phi2 = subst_prop_id (v2.x, v1.x) phi2 in
  let query = close_rtypeds_to_prop uqvs (smart_implies phi1 phi2) in
  (* let () = Printf.printf "query: %s\n" (layout_prop query) in *)
  let query =
    match v1.ty with Nt.Ty_unit -> query | _ -> Forall (v1, query)
  in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "query: %s\n" (layout_prop query)
  in
  let fvs = fv_prop query in
  let () =
    _assert __FILE__ __LINE__
      (spf "the cty query has free variables %s" (StrList.to_string fvs))
      (0 == List.length fvs)
  in
  Smtquery.cached_check_bool query
(* Smtquery.check_bool query *)

let sub_cty (pctx : RTypectx.ctx) (cty1, cty2) =
  let rec aux (pctx : RTypectx.ctx) uqvs cty1 cty2 =
    match RTypectx.last_destruct_opt pctx with
    | None -> aux_sub_cty uqvs cty1 cty2
    | Some (pctx, (rx, rty)) -> (
        match rty with
        | ArrRty _ -> aux pctx uqvs cty1 cty2
        | BaseRty { cty } -> aux pctx ({ cx = rx; cty } :: uqvs) cty1 cty2)
  in
  aux pctx [] cty1 cty2

let sub_cty_bool (pctx : RTypectx.ctx) (cty1, cty2) = sub_cty pctx (cty1, cty2)
(* match sub_cty pctx cty1 cty2 with None -> true | Some _ -> false *)

let is_bot_cty pctx cty =
  let bot_cty = Cty.(mk_bot (erase cty)) in
  sub_cty_bool pctx (cty, bot_cty)

let is_bot_rty pctx rty =
  match rty with BaseRty { cty } -> is_bot_cty pctx cty | ArrRty _ -> false
