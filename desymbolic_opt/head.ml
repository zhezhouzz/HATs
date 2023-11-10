open Zzdatatype.Datatype
open Language
open Language.Rty.P
open Sugar

type features = lit array

type head = {
  global_features : features;
  local_features : (string typed list * features) StrMap.t;
}

let pprint_tab m =
  if Array.length m == 0 then Pp.printf "Empty\n"
  else
    Array.iteri
      (fun idx lit -> Pp.printf "@{%i@}: %s, " idx (Rty.layout_lit lit))
      m;
  Pp.printf "\n"

let pprint_head { global_features; local_features } =
  let () = Pp.printf "[global_features]:" in
  let () = pprint_tab global_features in
  let () = Pp.printf "[local_features]:\n" in
  let () =
    StrMap.iter
      (fun op (_, m) ->
        let () = Pp.printf "[%s]: " op in
        pprint_tab m)
      local_features
  in
  ()

let build_euf vars =
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux ty vars =
    let pairs = List.combination_l vars 2 in
    let eqlits =
      List.map
        (fun l ->
          match l with
          | [ x; y ] -> L.mk_lit_eq_lit ty x y
          | _ -> _failatwith __FILE__ __LINE__ "die")
        pairs
    in
    eqlits
  in
  let res =
    Hashtbl.fold
      (fun ty vars res ->
        if List.length vars > 1 then aux ty vars @ res else res)
      space []
  in
  res

open Rty

let litlist_to_tab (vs, l) =
  let l = List.slow_rm_dup eq_lit l in
  (vs, Array.of_list l)

let make_tab addtional_global_lits regex =
  let g = gather regex in
  (* let num_lits = num_lits g in *)
  (* let () = record_max stat_max_lits num_lits in *)
  let { global_lits; local_lits } = g in
  let global_args =
    StrMap.map
      (fun (local_vars, lits) ->
        let local_vars = List.map (fun x -> x.x) local_vars in
        let args = List.concat @@ List.map L.get_op_args lits in
        let args =
          List.filter
            (fun lit ->
              match List.interset String.equal local_vars (L.fv_lit lit.x) with
              | [] -> true
              | _ -> false)
            args
        in
        args)
      local_lits
  in
  let global_args = List.concat @@ StrMap.to_value_list global_args in
  let global_args =
    List.slow_rm_dup (fun x y -> L.eq_lit x.x y.x) global_args
  in
  let () =
    Printf.printf "global_args: %s\n"
      (List.split_by_comma (fun x -> layout_lit x.x) global_args)
  in
  let euf_constraints = build_euf global_args in
  let global_features =
    Array.of_list
    @@ List.slow_rm_dup (fun x y -> L.eq_lit x y)
    @@ global_lits @ euf_constraints @ addtional_global_lits
  in
  let local_features = StrMap.map litlist_to_tab local_lits in
  let res = { global_features; local_features } in
  res

(* let mk_minterm_ids n = List.init (NRegex.pow 2 n) (fun x -> x) *)
(* let mk_minterms_from_tab m = mk_minterm_ids (tab_cardinal m) *)

(* let mk_mts { global_features; local_features } = *)
(*   let local_m = StrMap.map mk_minterms_from_tab local_features in *)
(*   let global_idxs = mk_minterms_from_tab global_features in *)
(*   let idxs = global_idxs in *)
(*   let m = *)
(*     List.fold_left (fun m idx -> IntMap.add idx local_m m) IntMap.empty idxs *)
(*   in *)
(*   m *)

let ctx_ctx_init _ regex =
  let tab = make_tab [] regex in
  let () = Env.show_log "desymbolic" @@ fun _ -> pprint_head tab in
  tab
(* let mts = mk_mts tab in *)
(* let () = Env.show_log "desymbolic" @@ fun _ -> NRegex.pprint_mts mts in *)
(* (tab, mts) *)
