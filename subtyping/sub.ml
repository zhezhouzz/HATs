open Language
open Zzdatatype.Datatype
open Sugar
open Rty

let debug_counter = ref 0

let rec sub_rty_bool rctx (rty1, rty2) =
  (* let () = *)
  (*   Printf.printf "R[%s]: %s\n" __FUNCTION__ *)
  (*     (RTypectx.layout_typed_l (fun x -> x) rctx) *)
  (* in *)
  match (rty1, rty2) with
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      Subcty.sub_cty_bool rctx (cty1, cty2)
  | ( ArrRty { arr = arr1; rethty = rethty1 },
      ArrRty { arr = arr2; rethty = rethty2 } ) -> (
      match sub_arr_bool rctx (arr1, arr2) with
      | None -> false
      | Some rctx' -> sub_hty_bool rctx' (rethty1, rethty2))
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_arr_bool rctx (arr1, arr2) =
  match (arr1, arr2) with
  | NormalArr para1, NormalArr para2 ->
      let para_bool = sub_rty_bool rctx (para2.rty, para1.rty) in
      if not para_bool then None
      else
        let () =
          _assert __FILE__ __LINE__ "subtyping should be unified"
            (String.equal para1.rx para2.rx)
        in
        let rctx' = RTypectx.new_to_right rctx para2 in
        Some rctx'
  | GhostArr para1, GhostArr para2 ->
      let () =
        _assert __FILE__ __LINE__ "subtyping should be unified"
          (String.equal para1.x para2.x)
      in
      let rctx' =
        RTypectx.new_to_right rctx { rx = para1.x; rty = mk_top para1.ty }
      in
      Some rctx'
  | ArrArr rty1, ArrArr rty2 ->
      let para_bool = sub_rty_bool rctx (rty2, rty1) in
      if not para_bool then None else Some rctx
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_hty_bool rctx (hty1, hty2) =
  match (hty1, hty2) with
  | Rty rty1, Rty rty2 -> sub_rty_bool rctx (rty1, rty2)
  | Rty rty1, Htriple { pre = pre2; resrty = rty2; post = post2 } ->
      if not (sub_rty_bool rctx (rty1, rty2)) then false
      else sub_srl_bool rctx (pre2, post2)
  | ( Htriple { pre = pre1; resrty = rty1; post = post1 },
      Htriple { pre = pre2; resrty = rty2; post = post2 } ) ->
      if not (sub_rty_bool rctx (rty1, rty2)) then false
      else if not (sub_srl_bool rctx (pre2, pre1)) then false
      else
        let post1' = LandA (SeqA (pre2, StarA AnyA), post1) in
        sub_srl_bool rctx (post1', post2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_srl_bool rctx (srl1, srl2) =
  (* let () = *)
  (*   Printf.printf "srl1: %s\n" (Sexplib.Sexp.to_string @@ sexp_of_srl srl1) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "srl2: %s\n" (Sexplib.Sexp.to_string @@ sexp_of_srl srl2) *)
  (* in *)
  let srl1' = simpl srl1 in
  (* let () = *)
  (*   Env.show_log "desymbolic" @@ fun _ -> *)
  (*   Pp.printf "@{<bold>[simpl] regex before:@} %s\n" (layout_regex srl1); *)
  (*   Pp.printf "@{<bold>[simpl] regex after:@} %s\n" (layout_regex srl1') *)
  (* in *)
  let srl2' = simpl srl2 in
  let res =
    match (srl1', srl2') with
    | EmptyA, _ | _, StarA AnyA -> true
    | _, EmptyA ->
        (* let () = Printf.printf "sdsd\n" in *)
        false
    | EpsilonA, EpsilonA -> true
    | srl1, srl2 -> sub_srl_bool_aux rctx (srl1, srl2)
  in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "R: %s\nResult:%b\n" (RTypectx.layout_typed_l rctx) res
  in
  res

and sub_srl_bool_aux rctx (srl1, srl2) =
  let () =
    Env.show_debug_info @@ fun _ ->
    Printf.printf "sub_srl_bool_aux R: %s\n" (RTypectx.layout_typed_l rctx)
  in
  let runtime, (ctx, mts) =
    Sugar.clock (fun () -> Desymbolic.ctx_ctx_init rctx (LorA (srl1, srl2)))
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
  (*             sub_rty_bool (RTypectx.new_to_rights rctx bindings) (tau1, tau2)) *)
  (*           ctx mt *)
  (*       in *)
  (*       if b then Some mt.NRegex.local_embedding else None) *)
  (*     mts *)
  (* in *)
  let mts =
    Desymbolic.filter_sat_mts ctx
      (fun bindings (tau1, tau2) ->
        sub_rty_bool (RTypectx.new_to_rights rctx bindings) (tau1, tau2))
      mts
  in
  let () = Env.show_debug_queries @@ fun _ -> NRegex.pprint_mts mts in
  let runtime1, srl1 =
    Sugar.clock (fun () -> Desymbolic.desymbolic ctx mts srl1)
  in
  let runtime2, srl2 =
    Sugar.clock (fun () -> Desymbolic.desymbolic ctx mts srl2)
  in
  let check (srl1, srl2) =
    let () =
      Env.show_debug_stat @@ fun _ ->
      Printf.printf "Desymbolic.desymbolic r1: %f\n" runtime1;
      Printf.printf "Desymbolic.desymbolic r2: %f\n" runtime2
    in
    let () =
      Env.show_debug_info @@ fun _ ->
      Pp.printf "@{<bold>Symbolic Automton 1:@} %s\n"
        (NRegex.reg_to_string srl1)
    in
    let () =
      Env.show_debug_info @@ fun _ ->
      Pp.printf "@{<bold>Symbolic Automton 2:@} %s\n"
        (NRegex.reg_to_string srl2)
    in
    let res = Smtquery.check_inclusion_counterexample (srl1, srl2) in
    (* let () = *)
    (*   if 1 == !debug_counter then failwith "end" *)
    (*   else debug_counter := !debug_counter + 1 *)
    (* in *)
    let res =
      match res with
      | None -> true
      | Some mt_list ->
          ( Env.show_debug_debug @@ fun _ ->
            Desymbolic.display_trace rctx ctx mt_list );
          false
    in
    let () =
      Env.show_debug_queries @@ fun _ ->
      Pp.printf "@{<bold>Inclusion Check Result:@} %b\n" res
    in
    res
  in
  let res = List.for_all check @@ _safe_combine __FILE__ __LINE__ srl1 srl2 in
  res

let is_bot_hty rctx = function
  | Rty rty -> Subcty.is_bot_rty rctx rty
  | _ -> _failatwith __FILE__ __LINE__ "die"
(* NOTE: cannot decide if it is botton at this point *)
(* | Sigmaty _ -> _failatwith __FILE__ __LINE__ "die" *)
