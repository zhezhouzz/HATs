open Language
open Zzdatatype.Datatype
open Sugar
open Rty

let debug_counter = ref 0

let rec sub_pty_bool pctx (pty1, pty2) =
  (* let () = *)
  (*   Printf.printf "R[%s]: %s\n" __FUNCTION__ *)
  (*     (PTypectx.layout_typed_l (fun x -> x) pctx) *)
  (* in *)
  match (pty1, pty2) with
  | BasePty { cty = cty1 }, BasePty { cty = cty2 } ->
      Subcty.sub_cty_bool pctx (cty1, cty2)
  | TuplePty taus1, TuplePty taus2 ->
      List.for_all (sub_pty_bool pctx)
      @@ _safe_combine __FILE__ __LINE__ taus1 taus2
  | ( ArrPty { arr_kind = PiArr; rarg = rarg1; retrty = retrty1 },
      ArrPty { arr_kind = PiArr; rarg = rarg2; retrty = retrty2 } ) ->
      let arg_bool = sub_pty_bool pctx (rarg2.pty, rarg1.pty) in
      let pctx' =
        match (rarg1.px, rarg2.px) with
        | None, None -> pctx
        | Some px, None | None, Some px ->
            PTypectx.new_to_right pctx { px; pty = rarg2.pty }
        | Some px, Some px' ->
            let () =
              _assert __FILE__ __LINE__ "subtyping should be unified"
                (String.equal px px')
            in
            PTypectx.new_to_right pctx { px; pty = rarg2.pty }
      in
      arg_bool && sub_rty_bool pctx' (retrty1, retrty2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_rty_bool pctx (rty1, rty2) =
  let sub_eff_rty_bool (a11, a12) (a21, a22) =
    sub_pre_regex_bool pctx (a21, a11) && sub_regex_bool pctx (a12, a22)
  in
  match (rty1, rty2) with
  | Pty pty1, Pty pty2 -> sub_pty_bool pctx (pty1, pty2)
  | ( Regty { prereg = a11; postreg = a12; _ },
      Regty { prereg = a21; postreg = a22; _ } ) ->
      sub_eff_rty_bool (a11, a12) (a21, a22)
  | Pty pty1, Regty _ -> sub_rty_bool pctx (pty_to_ret_rty pty1, rty2)
  | Regty _, Pty pty2 -> sub_rty_bool pctx (rty1, pty_to_ret_rty pty2)

and sub_pre_regex_bool pctx (a1, a2) = sub_regex_bool pctx (a1, a2)
(* match (a1, a2) with *)
(* | _, (starA anyA) -> true *)
(* | _, _ -> sub_regex_bool pctx (a1, a2) *)
(* sub_regex_bool pctx (SeqA (mk_regex_all, a1), SeqA (mk_regex_all, a2)) *)

and sub_regex_bool pctx (regex1, regex2) =
  (* let () = *)
  (*   Printf.printf "regex1: %s\n" (Sexplib.Sexp.to_string @@ sexp_of_regex regex1) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "regex2: %s\n" (Sexplib.Sexp.to_string @@ sexp_of_regex regex2) *)
  (* in *)
  let res =
    match (Auxtyping.simp regex1, Auxtyping.simp regex2) with
    | EmptyA, _ | _, StarA AnyA -> true
    | _, EmptyA ->
        (* let () = Printf.printf "sdsd\n" in *)
        false
    | EpsilonA, EpsilonA -> true
    | EventA (RetEvent pty1), EventA (RetEvent pty2) ->
        sub_pty_bool pctx (pty1, pty2)
    | regex1, regex2 -> sub_regex_bool_aux pctx (regex1, regex2)
  in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "R: %s\nResult:%b\n" (PTypectx.layout_typed_l pctx) res
  in
  res

and sub_regex_bool_aux pctx (regex1, regex2) =
  let () =
    Env.show_debug_info @@ fun _ ->
    Printf.printf "sub_regex_bool_aux R: %s\n" (PTypectx.layout_typed_l pctx)
  in
  let runtime, (ctx, mts) =
    Sugar.clock (fun () -> Desymbolic.ctx_init (LorA (regex1, regex2)))
  in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Printf.printf "Desymbolic.ctx_init: %f\n" runtime
  in
  (* let filter_sat_mts mts = *)
  (*   NRegex.mts_filter_map *)
  (*     (fun mt -> *)
  (*       let () = *)
  (*         Env.show_debug_queries @@ fun _ -> *)
  (*         Pp.printf "@{<bold>Minterm Check:@} %s\n" (NRegex.mt_to_string mt) *)
  (*       in *)
  (*       let b = *)
  (*         Desymbolic.minterm_verify_bool *)
  (*           (fun bindings (tau1, tau2) -> *)
  (*             sub_pty_bool (PTypectx.new_to_rights pctx bindings) (tau1, tau2)) *)
  (*           ctx mt *)
  (*       in *)
  (*       if b then Some mt.NRegex.local_embedding else None) *)
  (*     mts *)
  (* in *)
  let mts =
    Desymbolic.filter_sat_mts ctx
      (fun bindings (tau1, tau2) ->
        sub_pty_bool (PTypectx.new_to_rights pctx bindings) (tau1, tau2))
      mts
  in
  let () = Env.show_debug_queries @@ fun _ -> NRegex.pprint_mts mts in
  let runtime, regex1 =
    Sugar.clock (fun () -> Desymbolic.desymbolic ctx mts regex1)
  in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Printf.printf "Desymbolic.desymbolic r1: %f\n" runtime
  in
  let runtime, regex2 =
    Sugar.clock (fun () -> Desymbolic.desymbolic ctx mts regex2)
  in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Printf.printf "Desymbolic.desymbolic r2: %f\n" runtime
  in
  let () =
    Env.show_debug_info @@ fun _ ->
    Pp.printf "@{<bold>Symbolic Automton 1:@} %s\n"
      (NRegex.reg_to_string regex1)
  in
  let () =
    Env.show_debug_info @@ fun _ ->
    Pp.printf "@{<bold>Symbolic Automton 2:@} %s\n"
      (NRegex.reg_to_string regex2)
  in
  let res = Smtquery.check_inclusion_counterexample (regex1, regex2) in
  (* let () = *)
  (*   if 1 == !debug_counter then failwith "end" *)
  (*   else debug_counter := !debug_counter + 1 *)
  (* in *)
  let res =
    match res with
    | None -> true
    | Some mt_list ->
        ( Env.show_debug_debug @@ fun _ ->
          Desymbolic.display_trace pctx ctx mt_list );
        false
  in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Pp.printf "@{<bold>Inclusion Check Result:@} %b\n" res
  in
  res

let is_bot_rty pctx = function
  | Pty pty -> Subcty.is_bot_pty pctx pty
  | Regty _ -> _failatwith __FILE__ __LINE__ "die"
(* NOTE: cannot decide if it is botton at this point *)
(* | Sigmaty _ -> _failatwith __FILE__ __LINE__ "die" *)
