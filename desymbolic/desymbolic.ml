include Head
open Zzdatatype.Datatype
open Language
open Rty
open Sugar

let minterm_to_op_model { global_tab; local_tab }
    NRegex.{ op; global_embedding; local_embedding } =
  let global_m = tab_i_to_b global_tab global_embedding in
  let m = StrMap.find "minterm_to_op_model" local_tab op in
  let local_m = tab_i_to_b m local_embedding in
  (global_m, local_m)

let display_trace rctx ctx mt_list =
  match List.last_destruct_opt mt_list with
  | Some (mt_list, ret_mt) ->
      let global_m, _ = minterm_to_op_model ctx ret_mt in
      let mt_list =
        List.map
          (fun mt ->
            let _, m = minterm_to_op_model ctx mt in
            m)
          mt_list
      in
      let () = Printf.printf "Gamma:\n" in
      let () = Printf.printf "%s\n" @@ RTypectx.layout_typed_l rctx in
      let () = Printf.printf "Global:\n" in
      let () = pprint_bool_tab global_m in
      let () =
        List.iteri
          (fun idx m ->
            let () = Printf.printf "[<%i>]:\n" idx in
            let () = pprint_bool_tab m in
            ())
          mt_list
      in
      ()
  | None -> Printf.printf "Empty trace ϵ\n"

let stat_filter_time_record = ref []
let stat_num_candicate_minterm_record = ref []
let candicate_minterm_counter = ref 0

let stat_init () =
  stat_filter_time_record := [];
  stat_num_candicate_minterm_record := [];
  candicate_minterm_counter := 0

let stat_counter_reset () = candicate_minterm_counter := 0

let stat_update runtime =
  stat_filter_time_record := !stat_filter_time_record @ [ runtime ];
  stat_num_candicate_minterm_record :=
    !stat_num_candicate_minterm_record @ [ !candicate_minterm_counter ];
  candicate_minterm_counter := 0

let stat_get_cur () =
  (!stat_num_candicate_minterm_record, !stat_filter_time_record)

let model_verify_bool sub_rty_bool (global_m, local_m) =
  let () = candicate_minterm_counter := !candicate_minterm_counter + 1 in
  let bindings =
    let vs = tab_vs local_m in
    (* let vs = List.map (fun x -> x.x #:: (mk_top_rty x.ty)) vs in *)
    let m = merge_global_to_local global_m local_m in
    let rty = Rty.mk_unit_rty_from_prop @@ tab_to_prop m in
    let binding = { rx = Rename.unique "a"; rty } in
    vs @ [ binding ]
  in
  let lhs_rty = Rty.mk_top Nt.unit_ty in
  let rhs_rty = Rty.mk_bot Nt.unit_ty in
  (* let () = *)
  (*   Pp.printf "%s |- %s ≮: @{<bold>%s@}\n@{<bold>Result:@} ?\n" *)
  (*     (List.split_by_comma *)
  (*        (fun { rty; _ } -> spf "%s" (Rty.layout_rty rty)) *)
  (*        bindings) *)
  (*     (Rty.layout_rty lhs_rty) (Rty.layout_rty rhs_rty) *)
  (* in *)
  let b = not (sub_rty_bool bindings (lhs_rty, rhs_rty)) in
  let () =
    Env.show_log "desymbolic" @@ fun _ ->
    Pp.printf "%s |- %s ≮: @{<bold>%s@}\n@{<bold>Result:@} %b\n"
      (List.split_by_comma
         (fun { rty; _ } -> spf "%s" (Rty.layout_rty rty))
         bindings)
      (Rty.layout_rty lhs_rty) (Rty.layout_rty rhs_rty) b
  in
  (* let () = failwith "end" in *)
  (* let () = Pp.printf "@{<bold>if_valid: %b@}\n" b in *)
  b

let minterm_verify_bool sub_rty_bool ctx mt =
  let model = minterm_to_op_model ctx mt in
  model_verify_bool sub_rty_bool model

let op_models m prop =
  let rec aux prop =
    match prop with
    | Lit (AC (Const.B b)) -> b
    | Lit lit -> tab_models_lit m lit
    | Implies (a, b) -> (not (aux a)) || aux b
    | Ite (a, b, c) -> if aux a then aux b else aux c
    | Not a -> not (aux a)
    | And es -> List.for_all aux es
    | Or es -> List.exists aux es
    | Iff (a, b) -> aux (Implies (a, b)) && aux (Implies (b, a))
    | Forall _ | Exists _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux prop

(* let minterm_to_qualifier { optab; _ } (op, n) = *)
(*   let mt_map = StrMap.find "minterm die" optab op in *)
(*   let len = LitMap.cardinal mt_map.lit_to_idx in *)
(*   let l = id_to_bl len n [] in *)
(*   let props = *)
(*     List.mapi *)
(*       (fun i b -> *)
(*         let lit = Lit (IntMap.find "minterm die" mt_map.idx_to_lit i) in *)
(*         if b then lit else Not lit) *)
(*       l *)
(*   in *)
(*   And props *)

open Rty

let models_event ctx mt = function
  | GuardEvent phi ->
      let global_m, _ = minterm_to_op_model ctx mt in
      op_models global_m phi
  | EffEvent { op; phi; _ } ->
      if String.equal mt.NRegex.op op then
        let global_m, local_m = minterm_to_op_model ctx mt in
        let m = merge_global_to_local global_m local_m in
        op_models m phi
      else false

let se_get_op = function
  | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
  | EffEvent { op; _ } -> op

let se_force_op = function
  | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
  | EffEvent { op; vs; v; phi } -> (op, vs, v, phi)

let desymbolic_sevent ctx (mts, g) se =
  let open NRegex in
  match se with
  | GuardEvent phi ->
      (* let l = mts_to_global_m mts in *)
      (* let l = *)
      (*   List.filter *)
      (*     (fun global_embedding -> *)
      (*       let m = tab_i_to_b ctx.global_tab global_embedding in *)
      (*       op_models m phi) *)
      (*     l *)
      (* in *)
      let mts =
        NRegex.mts_local_fold g
          (fun mt res ->
            let m = tab_i_to_b ctx.global_tab mt.global_embedding in
            if op_models m phi then NRegex.Minterm mt :: res else res)
          mts []
      in
      if List.length mts > 0 then Union mts else Empt
  | _ ->
      let op = se_get_op se in
      let mts =
        NRegex.mts_local_fold_on_op g op
          (fun mt res ->
            if models_event ctx mt se then NRegex.Minterm mt :: res else res)
          mts []
      in
      if List.length mts > 0 then Union mts else Empt

(* NOTE: the None indicate the emrty set *)
let desymbolic_local ctx (mts, g) regex =
  let open NRegex in
  let () =
    Env.show_log "regex_simpl" @@ fun _ ->
    Pp.printf "@{<bold>regex before:@} %s\n" (layout_regex regex)
  in
  let rec aux regex =
    match regex with
    | EmptyA -> Empt
    | AnyA ->
        Any
        (* let mts = *)
        (*   NRegex.mts_local_fold g *)
        (*     (fun mt res -> NRegex.Minterm mt :: res) *)
        (*     mts [] *)
        (* in *)
        (* if List.length mts > 0 then Union mts else Empt *)
    | EpsilonA -> Epsilon
    | EventA se -> desymbolic_sevent ctx (mts, g) se
    | LorA (t1, t2) -> Union [ aux t1; aux t2 ]
    | SetMinusA (t1, t2) -> Diff (aux t1, aux t2)
    | LandA (t1, t2) -> Intersect [ aux t1; aux t2 ]
    | SeqA (t1, t2) -> Concat [ aux t1; aux t2 ]
    | StarA t -> Star (aux t)
    | ComplementA t -> Complement (aux t)
  in
  let res = aux regex in
  let () =
    Env.show_log "regex_simpl" @@ fun _ ->
    Pp.printf "@{<bold>regex after:@} %s\n" (reg_to_string res)
  in
  let res = simp res in
  let () =
    Env.show_log "regex_simpl" @@ fun _ ->
    Pp.printf "@{<bold>regex simpl:@} %s\n" (reg_to_string res)
  in
  res

let desymbolic ctx mts regex =
  (* let open NRegex in *)
  let ress =
    IntMap.to_value_list
    @@ IntMap.mapi (fun g _ -> desymbolic_local ctx (mts, g) regex) mts
  in
  ress

(* let get_max_lits () = *)
(*   let n = !Head.stat_max_lits in *)
(*   if n == 0 then 1 else n *)

let filter_sat_mts_ ctx sub_rty_bool_with_binding mts =
  NRegex.mts_filter_map
    (fun mt ->
      let () =
        Env.show_log "desymbolic" @@ fun _ ->
        Pp.printf "@{<bold>Minterm Check:@} %s\n" (NRegex.mt_to_string mt)
      in
      let b = minterm_verify_bool sub_rty_bool_with_binding ctx mt in
      if b then Some mt.NRegex.local_embedding else None)
    mts

let filter_sat_mts ctx sub_rty_bool_with_binding mts =
  let _ = stat_counter_reset () in
  let runtime, mts =
    Sugar.clock (fun () -> filter_sat_mts_ ctx sub_rty_bool_with_binding mts)
  in
  let () = stat_update runtime in
  let () =
    Env.show_debug_stat @@ fun _ -> Printf.printf "filter_sat_mts: %f\n" runtime
  in
  mts
