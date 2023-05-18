open Language
open Zzdatatype.Datatype
open Sugar

(* open Auxtyping *)
open PCtxType

let rec sub_pty_bool pctx eqctx pty1 pty2 =
  (* let () = *)
  (*   Printf.printf "R[%s]: %s\n" __FUNCTION__ *)
  (*     (PTypectx.layout_typed_l (fun x -> x) pctx) *)
  (* in *)
  match (pty1, pty2) with
  | BasePty { cty = cty1 }, BasePty { cty = cty2 } ->
      Subcty.sub_cty_bool pctx cty1 cty2
  | TuplePty taus1, TuplePty taus2 ->
      List.for_all (fun (tau1, tau2) -> sub_pty_bool pctx eqctx tau1 tau2)
      @@ _safe_combine __FILE__ __LINE__ taus1 taus2
  | ( ArrPty { rarg = rarg1; retrty = retrty1 },
      ArrPty { rarg = rarg2; retrty = retrty2 } ) -> (
      let arg_bool = sub_pty_bool pctx eqctx rarg2.pty rarg1.pty in
      arg_bool
      &&
      match (rarg1.px, rarg2.px) with
      | None, None -> sub_rty_bool pctx eqctx retrty1 retrty2
      | Some x, None | None, Some x ->
          let pctx = PTypectx.new_to_right pctx { x; ty = rarg2.pty } in
          sub_rty_bool pctx eqctx retrty1 retrty2
      | Some x1, Some x ->
          let retrty1 = subst_id (x1, x) retrty1 in
          let pctx = PTypectx.new_to_right pctx { x; ty = rarg2.pty } in
          sub_rty_bool pctx eqctx retrty1 retrty2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_rty_bool pctx eqctx rty1 rty2 =
  match (rty1, rty2) with
  | Pty pty1, Pty pty2 -> sub_pty_bool pctx eqctx pty1 pty2
  | Regty regex1, Regty regex2 -> sub_regex_bool pctx eqctx regex1 regex2
  | Pty pty1, Regty _ -> sub_rty_bool pctx eqctx (pty_to_ret_rty pty1) rty2
  | Regty _, Pty pty2 -> sub_rty_bool pctx eqctx rty1 (pty_to_ret_rty pty2)
(* | Sigmaty _, _ | _, Sigmaty _ -> _failatwith __FILE__ __LINE__ "die" *)

and sub_regex_bool pctx eqctx regex1 regex2 =
  let () =
    Printf.printf "R: %s\n" (PTypectx.layout_typed_l (fun x -> x) pctx)
  in
  let regex1 = regex1.Nt.x in
  let regex2 = regex2.Nt.x in
  let ctx, mts = Desymbolic.ctx_init (LorA (regex1, regex2)) in
  let mts =
    NRegex.mts_filter_map
      (fun mt ->
        let () =
          Pp.printf "@{<bold>Minterm Check:@} %s\n" (NRegex.mt_to_string mt)
        in
        let b =
          Desymbolic.minterm_verify_bool
            (fun bindings (tau1, tau2) ->
              sub_pty_bool
                (PTypectx.new_to_rights pctx bindings)
                eqctx tau1 tau2)
            ctx mt
        in
        if b then Some mt.NRegex.local_embedding else None)
      mts
  in
  let () = NRegex.pprint_mts mts in
  let regex1 = Desymbolic.desymbolic ctx mts regex1 in
  let regex2 = Desymbolic.desymbolic ctx mts regex2 in
  let () =
    Pp.printf "@{<bold>Symbolic Automton 1:@} %s\n"
      (NRegex.reg_to_string regex1)
  in
  let () =
    Pp.printf "@{<bold>Symbolic Automton 2:@} %s\n"
      (NRegex.reg_to_string regex2)
  in
  (* let () = failwith "end" in *)
  let res = Smtquery.check_inclusion_counterexample (regex1, regex2) in
  let res =
    match res with
    | None -> true
    | Some mt_list ->
        Desymbolic.display_trace pctx ctx mt_list;
        false
  in
  let () = Pp.printf "@{<bold>Inclusion Check Result:@} %b\n" res in
  res

let is_bot_rty pctx _ = function
  | Pty pty -> Subcty.is_bot_pty pctx pty
  | Regty _ -> false
(* NOTE: cannot decide if it is botton at this point *)
(* | Sigmaty _ -> _failatwith __FILE__ __LINE__ "die" *)
