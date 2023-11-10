include Head
open Zzdatatype.Datatype
open Language

(* open Rty *)
open Sugar

(* let minterm_to_op_model { global_tab; local_tab } *)
(*     NRegex.{ op; global_embedding; local_embedding } = *)
(*   let global_m = tab_i_to_b global_tab global_embedding in *)
(*   let m = StrMap.find "minterm_to_op_model" local_tab op in *)
(*   let local_m = tab_i_to_b m local_embedding in *)
(*   (global_m, local_m) *)

(* let display_trace rctx ctx mt_list = *)
(*   match List.last_destruct_opt mt_list with *)
(*   | Some (mt_list, ret_mt) -> *)
(*       let global_m, _ = minterm_to_op_model ctx ret_mt in *)
(*       let mt_list = *)
(*         List.map *)
(*           (fun mt -> *)
(*             let _, m = minterm_to_op_model ctx mt in *)
(*             m) *)
(*           mt_list *)
(*       in *)
(*       let () = Printf.printf "Gamma:\n" in *)
(*       let () = Printf.printf "%s\n" @@ RTypectx.layout_typed_l rctx in *)
(*       let () = Printf.printf "Global:\n" in *)
(*       let () = pprint_bool_tab global_m in *)
(*       let () = *)
(*         List.iteri *)
(*           (fun idx m -> *)
(*             let () = Printf.printf "[<%i>]:\n" idx in *)
(*             let () = pprint_bool_tab m in *)
(*             ()) *)
(*           mt_list *)
(*       in *)
(*       () *)
(*   | None -> Printf.printf "Empty trace ϵ\n" *)

(* let stat_filter_time_record = ref [] *)
(* let stat_num_candicate_minterm_record = ref [] *)
(* let candicate_minterm_counter = ref 0 *)

(* let stat_init () = *)
(*   stat_filter_time_record := []; *)
(*   stat_num_candicate_minterm_record := []; *)
(*   candicate_minterm_counter := 0 *)

(* let stat_counter_reset () = candicate_minterm_counter := 0 *)

(* let stat_update runtime = *)
(*   stat_filter_time_record := !stat_filter_time_record @ [ runtime ]; *)
(*   stat_num_candicate_minterm_record := *)
(*     !stat_num_candicate_minterm_record @ [ !candicate_minterm_counter ]; *)
(*   candicate_minterm_counter := 0 *)

(* let stat_get_cur () = *)
(*   (!stat_num_candicate_minterm_record, !stat_filter_time_record) *)

let model_verify_bool sub_rty_bool (vs, prop) =
  let bindings =
    let vs = List.map (fun {x; ty} -> {rx = x; rty = Rty.mk_top ty}) vs in
    let rty = Rty.mk_unit_rty_from_prop prop in
    let binding = { rx = Rename.unique "a"; rty } in
    vs @ [ binding ]
  in
  let lhs_rty = Rty.mk_top Nt.unit_ty in
  let rhs_rty = Rty.mk_bot Nt.unit_ty in
  let b = not (sub_rty_bool bindings (lhs_rty, rhs_rty)) in
  let () =
    Env.show_log "desymbolic" @@ fun _ ->
    Pp.printf "%s |- %s ≮: @{<bold>%s@}\n@{<bold>Result:@} %b\n"
      (List.split_by_comma
         (fun { rty; _ } -> spf "%s" (Rty.layout_rty rty))
         bindings)
      (Rty.layout_rty lhs_rty) (Rty.layout_rty rhs_rty) b
  in
  b

(* let minterm_verify_bool sub_rty_bool ctx mt = *)
(*   let model = minterm_to_op_model ctx mt in *)
(*   model_verify_bool sub_rty_bool model *)

open Rty

let partial_evaluate_lit global_tab lit =
  match Hashtbl.find_opt global_tab lit with
  | Some b -> AC (Const.B b)
  | None -> lit

let partial_evaluate_prop global_tab prop =
  let rec aux prop =
    match prop with
    | Lit lit -> Lit (partial_evaluate_lit global_tab lit)
    | Implies (a, b) -> Implies (aux a, aux b)
    | Ite (a, b, c) -> Ite (aux a, aux b, aux c)
    | Not a -> Not (aux a)
    | And es -> And (List.map aux es)
    | Or es -> Or (List.map aux es)
    | Iff (a, b) -> Iff (aux a, aux b)
    | Forall _ | Exists _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux prop

let models_lit tab lit =
  match Hashtbl.find_opt tab lit with
  | Some b -> b
  | None -> _failatwith __FILE__ __LINE__ "tab_models_lit"

let models_prop m prop =
  let rec aux prop =
    match prop with
    | Lit (AC (Const.B b)) -> b
    | Lit lit -> models_lit m lit
    | Implies (a, b) -> (not (aux a)) || aux b
    | Ite (a, b, c) -> if aux a then aux b else aux c
    | Not a -> not (aux a)
    | And es -> List.for_all aux es
    | Or es -> List.exists aux es
    | Iff (a, b) -> aux (Implies (a, b)) && aux (Implies (b, a))
    | Forall _ | Exists _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux prop

let partial_evaluate_sevent global_tab se =
  (* let open NRegex in *)
  match se with
  | GuardEvent phi -> if models_prop global_tab phi then AnyA else EmptyA
  | EffEvent { op; vs; v; phi } ->
      let phi = partial_evaluate_prop global_tab phi in
      EventA (EffEvent { op; vs; v; phi })

let partial_evaluate_regex global_tab regex =
  let () =
    Env.show_log "regex_simpl" @@ fun _ ->
    Pp.printf "@{<bold>regex before:@} %s\n" (layout_regex regex)
  in
  let rec aux regex =
    match regex with
    | EmptyA | AnyA | EpsilonA -> regex
    | EventA se -> partial_evaluate_sevent global_tab se
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | StarA t -> StarA (aux t)
    | ComplementA t -> ComplementA (aux t)
  in
  let res = aux regex in
  res

let desymbolic_sevent global_embedding dts se =
  let open NRegex in
  match se with
  | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
  | EffEvent { op; phi; _ } ->
      let local_m = StrMap.find "desymbolic_sevent" dts op in
      let mts =
        List.filter_map
          (fun (idx, local_tab) ->
            if models_prop local_tab phi then Some idx else None)
          local_m
      in
      let mts =
        List.map
          (fun local_embedding ->
            Minterm { op; global_embedding; local_embedding })
          mts
      in
      if List.length mts > 0 then Union mts else Empt

(* NOTE: the None indicate the emrty set *)
let desymbolic_local global_embedding dts regex =
  let open NRegex in
  let () =
    Env.show_log "regex_simpl" @@ fun _ ->
    Pp.printf "@{<bold>regex before:@} %s\n" (layout_regex regex)
  in
  let rec aux regex =
    match regex with
    | EmptyA -> Empt
    | AnyA -> Any
    | EpsilonA -> Epsilon
    | EventA se -> desymbolic_sevent global_embedding dts se
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

type mt_tabs = (int * (lit, bool) Hashtbl.t) list

type all_mt_tabs = {
  global_tab : mt_tabs;
  local_tabs : mt_tabs StrMap.t IntMap.t;
}

type all_dt = { global_dt : DT.t; local_dts : DT.t StrMap.t IntMap.t }

let all_to_tab { global_features; local_features } { global_dt; local_dts } =
  let global_tab = DT.dt_to_tab (global_features, global_dt) in
  let local_tabs =
    IntMap.map
      (fun m ->
        StrMap.mapi
          (fun op x ->
            let local_feature = StrMap.find "all_to_tab" local_features op in
            DT.dt_to_tab (snd local_feature, x))
          m)
      local_dts
  in
  (* let local_tabs = IntMap.to_value_list local_tabs in *)
  { global_tab; local_tabs }

let desymbolic { global_tab; local_tabs } regex =
  List.map
    (fun (global_embedding, global_m) ->
       let regex' = partial_evaluate_regex global_m regex in
       let dts = IntMap.find "desymbolic" local_tabs global_embedding in
       desymbolic_local global_embedding dts regex')
    global_tab

let mk_mt_tab sat_checker { global_features; local_features } =
  let global_dt = DT.dynamic_classify sat_checker global_features in
  let local_dts = StrMap.map (fun (vs, features) ->
      DT.dynamic_classify sat_checker features
    ) local_features in
  let global_tab = DT.dt_to_tab (global_features, global_dt) in


(* let filter_sat_mts_ ctx sub_rty_bool_with_binding mts = *)
(*   NRegex.mts_filter_map *)
(*     (fun mt -> *)
(*       let () = *)
(*         Env.show_log "desymbolic" @@ fun _ -> *)
(*         Pp.printf "@{<bold>Minterm Check:@} %s\n" (NRegex.mt_to_string mt) *)
(*       in *)
(*       let b = minterm_verify_bool sub_rty_bool_with_binding ctx mt in *)
(*       if b then Some mt.NRegex.local_embedding else None) *)
(*     mts *)

(* let filter_sat_mts ctx sub_rty_bool_with_binding mts = *)
(*   let _ = stat_counter_reset () in *)
(*   let runtime, mts = *)
(*     Sugar.clock (fun () -> filter_sat_mts_ ctx sub_rty_bool_with_binding mts) *)
(*   in *)
(*   let () = stat_update runtime in *)
(*   let () = *)
(*     Env.show_debug_stat @@ fun _ -> Printf.printf "filter_sat_mts: %f\n" runtime *)
(*   in *)
(*   mts *)
