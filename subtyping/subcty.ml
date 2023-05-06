open Language
open Rty
open Zzdatatype.Datatype
open Sugar
open Auxtyping

let close_ptyped_to_prop { cx; cty = { v; phi } } prop =
  let open P in
  let xphi = subst_prop_id (v.x, cx) phi in
  let x = cx #: v.ty in
  smart_sigma (x, xphi) prop

let close_ptypeds_to_prop l prop = List.fold_right close_ptyped_to_prop l prop

let aux_sub_cty uqvs { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  let open P in
  let phi2 = subst_prop_id (v2.x, v1.x) phi2 in
  let query = close_ptypeds_to_prop uqvs (smart_implies phi1 phi2) in
  let query = Forall (v1, query) in
  Smtquery.check query

let sub_cty rctx cty1 cty2 =
  let rec aux rctx uqvs cty1 cty2 =
    match List.last_destruct_opt rctx with
    | None -> aux_sub_cty uqvs cty1 cty2
    | Some (rctx, x) -> (
        let x = typed_force_to_ptyped __FILE__ __LINE__ x in
        match x.pty with
        | TuplePty _ ->
            _failatwith __FILE__ __LINE__ "unimp: tuple type in the ctx"
        | ArrPty _ -> aux rctx uqvs cty1 cty2
        | BasePty { ou = Over; cty } ->
            aux rctx ({ cx = x.px; cty } :: uqvs) cty1 cty2
        | BasePty { ou = Under; _ } ->
            let cty1 = exists_ptyped_to_cty x cty1 in
            let cty2 = exists_ptyped_to_cty x cty2 in
            aux rctx uqvs cty1 cty2)
  in
  aux rctx [] cty1 cty2

let sub_cty_bool rctx cty1 cty2 =
  match sub_cty rctx cty1 cty2 with None -> true | Some _ -> false

let is_bot_cty rctx cty =
  let bot_cty = mk_bot_cty (erase_cty cty) in
  sub_cty_bool rctx cty bot_cty

let is_bot_pty rctx pty =
  match pty with
  | TuplePty _ -> _failatwith __FILE__ __LINE__ "die"
  | BasePty { ou = Over; _ } -> false
  | BasePty { ou = Under; cty } -> is_bot_cty rctx cty
  | ArrPty _ -> false
