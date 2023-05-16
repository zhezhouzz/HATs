open Language
open Zzdatatype.Datatype
open Sugar

(* open Auxtyping *)
open Rty

(* let merge_effect_binding rctx (rty1, rty2) = *)
(*   let rctx = *)
(*     List.filter *)
(*       (fun x -> match x.ty with Pty (ArrPty _) -> false | _ -> true) *)
(*       rctx *)
(*   in *)
(*   let rec aux gamma1 gamma2 (rty1, rty2) = *)
(*     match List.last_destruct_opt gamma1 with *)
(*     | None -> (gamma2, (rty1, rty2)) *)
(*     | Some (gamma1, binding) -> ( *)
(*         match binding with *)
(*         | { ty = Pty (ArrPty _); _ } -> _failatwith __FILE__ __LINE__ "die" *)
(*         | { ty = Pty (TuplePty _); _ } -> _failatwith __FILE__ __LINE__ "die" *)
(*         | { ty = Pty (BasePty _); _ } -> *)
(*             (gamma1 @ [ binding ] @ gamma2, (rty1, rty2)) *)
(*         | { ty = Regty _; _ } -> *)
(*             _failatwith __FILE__ __LINE__ "die" *)
(*             (\* let rty1 = Auxtyping.exists_typed binding rty1 in *\) *)
(*             (\* let rty2 = Auxtyping.exists_typed binding rty2 in *\) *)
(*             (\* aux gamma1 gamma2 (rty1, rty2) *\)) *)
(*   in *)
(*   aux rctx [] (rty1, rty2) *)

(* let sub_regex_purify gamma eqctx regex1 regex2 = *)
(*   let check gamma prop = *)
(*     not (Subcty.is_bot_pty gamma (mk_unit_under_pty_from_prop prop)) *)
(*   in *)
(*   let topl1, regex1 = Auxtyping.purify eqctx gamma check regex1 in *)
(*   let topl2, regex2 = Auxtyping.purify eqctx gamma check regex2 in *)
(*   let topl2 = List.map (fun x -> x.x #: (rty_flip x.ty)) topl2 in *)
(*   let gamma = topl2 @ gamma @ topl1 in *)
(*   (gamma, eqctx, regex1, regex2) *)

let rec sub_pty_bool rctx eqctx pty1 pty2 =
  match (pty1, pty2) with
  | BasePty { cty = cty1 }, BasePty { cty = cty2 } ->
      Subcty.sub_cty_bool rctx cty1 cty2
  | TuplePty taus1, TuplePty taus2 ->
      List.for_all (fun (tau1, tau2) -> sub_pty_bool rctx eqctx tau1 tau2)
      @@ _safe_combine __FILE__ __LINE__ taus1 taus2
  | ( ArrPty { rarg = rarg1; retrty = retrty1 },
      ArrPty { rarg = rarg2; retrty = retrty2 } ) -> (
      let arg_bool = sub_pty_bool rctx eqctx rarg2.pty rarg1.pty in
      arg_bool
      &&
      match (rarg1.px, rarg2.px) with
      | None, None -> sub_rty_bool rctx eqctx retrty1 retrty2
      | Some x, None | None, Some x ->
          let rctx = RTypectx.new_to_right rctx { x; ty = Pty rarg2.pty } in
          sub_rty_bool rctx eqctx retrty1 retrty2
      | Some x1, Some x ->
          let retrty1 = subst_id (x1, x) retrty1 in
          let rctx = RTypectx.new_to_right rctx { x; ty = Pty rarg2.pty } in
          sub_rty_bool rctx eqctx retrty1 retrty2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_rty_bool rctx eqctx rty1 rty2 =
  match (rty1, rty2) with
  | Pty pty1, Pty pty2 -> sub_pty_bool rctx eqctx pty1 pty2
  | Regty regex1, Regty regex2 -> sub_regex_bool rctx eqctx regex1 regex2
  | Pty pty1, Regty _ -> sub_rty_bool rctx eqctx (pty_to_ret_rty pty1) rty2
  | Regty _, Pty pty2 -> sub_rty_bool rctx eqctx rty1 (pty_to_ret_rty pty2)
(* | Sigmaty _, _ | _, Sigmaty _ -> _failatwith __FILE__ __LINE__ "die" *)

and sub_regex_bool rctx eqctx regex1 regex2 =
  (* let rctx, (regex1, regex2) = *)
  (*   match merge_effect_binding rctx (Regty regex1, Regty regex2) with *)
  (*   | rctx, (Regty regex1, Regty regex2) -> (rctx, (regex1, regex2)) *)
  (*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
  (* in *)
  (* let rctx, eqctx, regex1, regex2 = sub_regex_purify rctx eqctx regex1 regex2 in *)
  let regex1 = regex1.Nt.x in
  let regex2 = regex2.Nt.x in
  let () =
    Printf.printf "R: %s\n" (RTypectx.layout_typed_l (fun x -> x) rctx)
  in
  let ctx, mts = Desymbolic.ctx_init (LorA (regex1, regex2)) in
  (* let () = failwith "end" in *)
  let mts =
    NRegex.mts_filter_map
      (fun mt ->
        let b =
          Desymbolic.minterm_verify_bool
            (fun bindings (tau1, tau2) ->
              sub_pty_bool (rctx @ bindings) eqctx tau1 tau2)
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
  let res = Smtquery.check_inclusion_counterexample (regex2, regex1) in
  match res with
  | None -> true
  | Some mt_list ->
      Desymbolic.display_trace rctx ctx mt_list;
      false

let is_bot_rty rctx _ = function
  | Pty pty -> Subcty.is_bot_pty rctx pty
  | Regty _ -> false
(* NOTE: cannot decide if it is botton at this point *)
(* | Sigmaty _ -> _failatwith __FILE__ __LINE__ "die" *)
