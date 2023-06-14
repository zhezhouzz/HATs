open Language
open Rty
open Zzdatatype.Datatype
open Sugar
(* open Auxtyping *)

let close_ptyped_to_prop x prop =
  let open P in
  let x, phix = cty_typed_to_prop x in
  smart_pi (x, phix) prop

let close_ptypeds_to_prop l prop = List.fold_right close_ptyped_to_prop l prop

let aux_sub_cty uqvs { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  let open P in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "uqvs: %s\n"
    @@ List.split_by_comma
         (fun { cx; cty } -> spf "%s:%s" cx @@ layout_cty cty)
         uqvs
  in
  let phi2 = subst_prop_id (v2.x, v1.x) phi2 in
  let query = close_ptypeds_to_prop uqvs (smart_implies phi1 phi2) in
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
  Smtquery.check_bool query

let sub_cty (pctx : PTypectx.ctx) (cty1, cty2) =
  let rec aux (pctx : PTypectx.ctx) uqvs cty1 cty2 =
    match PTypectx.last_destruct_opt pctx with
    | None -> aux_sub_cty uqvs cty1 cty2
    | Some (pctx, (px, pty)) -> (
        match pty with
        | TuplePty _ ->
            _failatwith __FILE__ __LINE__ "unimp: tuple type in the ctx"
        | ArrPty _ -> aux pctx uqvs cty1 cty2
        | BasePty { cty } -> aux pctx ({ cx = px; cty } :: uqvs) cty1 cty2)
  in
  aux pctx [] cty1 cty2

let sub_cty_bool (pctx : PTypectx.ctx) (cty1, cty2) = sub_cty pctx (cty1, cty2)
(* match sub_cty pctx cty1 cty2 with None -> true | Some _ -> false *)

let is_bot_cty pctx cty =
  let bot_cty = mk_bot_cty (erase_cty cty) in
  sub_cty_bool pctx (cty, bot_cty)

let is_bot_pty pctx pty =
  match pty with
  | TuplePty _ -> _failatwith __FILE__ __LINE__ "die"
  | BasePty { cty } -> is_bot_cty pctx cty
  | ArrPty _ -> false
