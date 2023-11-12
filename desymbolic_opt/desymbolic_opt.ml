include Head
open Zzdatatype.Datatype
open Language
open Sugar
open Rty

let model_verify_bool sub_rty_bool (vs, prop) =
  let bindings =
    let vs = List.map (fun { x; ty } -> { rx = x; rty = Rty.mk_top ty }) vs in
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

let tab_to_prop tab =
  let res =
    Hashtbl.fold
      (fun lit b res -> if b then Lit lit :: res else Not (Lit lit) :: res)
      tab []
  in
  And res

let print_opt_stat (num, test_num) features =
  let total_fv = Sugar.pow 2 (Array.length features) in
  Printf.printf "valid(%i/%i); cost(%i/%i = %f)\n" num total_fv test_num
    total_fv
    (float_of_int test_num /. float_of_int total_fv)

let mk_mt_tab sub_rty_bool { global_features; local_features } =
  (* let local_features_array = *)
  (*   StrMap.map (fun (_, features) -> Array.of_list features) local_features *)
  (* in *)
  let () =
    Env.show_log "desymbolic" @@ fun _ ->
    Printf.printf "[Global DT]:\n";
    Head.pprint_tab global_features
  in
  let test_num, global_dt =
    DT.dynamic_classify
      (fun prop -> model_verify_bool sub_rty_bool ([], prop))
      global_features
  in
  let global_tab = DT.dt_to_tab (global_features, global_dt) in
  let () =
    Env.show_log "desymbolic" @@ fun _ ->
    Printf.printf "[Global DT]\n";
    print_opt_stat (List.length global_tab, test_num) global_features
  in
  let local_dts =
    StrMap.mapi
      (fun op (vs, features) ->
        let () =
          Env.show_log "desymbolic" @@ fun _ ->
          Printf.printf "[%s DT]:\n" op;
          Head.pprint_tab features
        in
        let test_num, dt =
          DT.dynamic_classify
            (fun prop -> model_verify_bool sub_rty_bool (vs, prop))
            features
        in
        let () =
          Env.show_log "desymbolic" @@ fun _ ->
          Printf.printf "[%s DT]\n" op;
          print_opt_stat (0, test_num) features
        in
        (vs, dt))
      local_features
  in
  let global_tab_with_local =
    List.map
      (fun (idx, tab) ->
        let prop = tab_to_prop tab in
        let dts =
          StrMap.mapi
            (fun op (vs, dt) ->
              let features = snd @@ StrMap.find "mk_mt_tab" local_features op in
              let () =
                Env.show_log "desymbolic" @@ fun _ ->
                Printf.printf "[Refine %s DT]:\n[Under]:%s\n" op
                  (layout_prop prop);
                Head.pprint_tab features
              in
              let test_num, dt =
                DT.refine_dt_under_prop
                  (fun prop -> model_verify_bool sub_rty_bool (vs, prop))
                  prop (features, dt)
              in
              let dt = DT.dt_to_tab (features, dt) in
              let () =
                Env.show_log "desymbolic" @@ fun _ ->
                Printf.printf "[Refine %s DT]\n" op;
                print_opt_stat (List.length dt, test_num) features
              in
              dt)
            local_dts
        in
        (idx, tab, dts))
      global_tab
  in
  global_tab_with_local

let desymbolic_under_global (global_embedding, global_m, dts) regex =
  let regex' = partial_evaluate_regex global_m regex in
  desymbolic_local global_embedding dts regex'

(* let filter_mts sub_rty_bool head = *)
(*   let tab = mk_mt_tab sub_rty_bool head in *)
(*   List.map (fun tab -> desymbolic_under_global tab regex) tab *)

let desymbolic tab regex =
  List.map (fun tab -> desymbolic_under_global tab regex) tab

let do_desymbolic checker (srl1, srl2) =
  let head = ctx_ctx_init (LorA (srl1, srl2)) in
  let () = Env.show_log "desymbolic" @@ fun _ -> Head.pprint_head head in
  let mt_tab = mk_mt_tab checker head in
  let srl1 = desymbolic mt_tab srl1 in
  let srl2 = desymbolic mt_tab srl2 in
  let res = _safe_combine __FILE__ __LINE__ srl1 srl2 in
  res
