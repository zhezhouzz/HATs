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
        if List.length vars > 1 && not (Nt.eq ty (Nt.Ty_uninter "Bytes.t")) then
          aux ty vars @ res
        else res)
      space []
  in
  res

open Rty

let litlist_to_tab (vs, l) =
  let l = List.slow_rm_dup eq_lit l in
  (vs, Array.of_list l)

let build_partial_one partial_func vars =
  let tys, _ = Nt.destruct_arr_tp partial_func.ty in
  let ty = List.nth tys 0 in
  let vars = List.filter (fun lit -> Nt.eq lit.ty ty) vars in
  let pairs = List.combination_l vars 2 in
  let plits = List.map (fun l -> L.AAppOp (partial_func, l)) pairs in
  plits

let build_partial partial_funcs vars =
  List.concat @@ List.map (fun f -> build_partial_one f vars) partial_funcs

let get_partail_op lits =
  let lits = List.concat @@ StrMap.to_value_list @@ StrMap.map snd lits in
  let aux = function
    | AAppOp (f, l) when not (String.equal (Op.to_string f.x) "==") -> (
        match l with [ a; b ] when Nt.eq a.ty b.ty -> Some f | _ -> None)
    | _ -> None
  in
  let res = List.filter_map aux lits in
  List.slow_rm_dup (fun a b -> Op.eq a.x b.x) res

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
    Env.show_log "desymbolic" @@ fun _ ->
    Printf.printf "global_args: %s\n"
      (List.split_by_comma (fun x -> layout_lit x.x) global_args)
  in
  let euf_constraints = build_euf global_args in
  let pops = get_partail_op local_lits in
  let () =
    Env.show_log "desymbolic" @@ fun _ ->
    Printf.printf "pops: %s\n"
    @@ List.split_by_comma (fun x -> Op.to_string x.x) pops
  in
  let partial_constraints = build_partial pops global_args in
  let global_features =
    Array.of_list
    @@ List.slow_rm_dup (fun x y -> L.eq_lit x y)
    @@ global_lits @ euf_constraints @ addtional_global_lits
    @ partial_constraints
  in
  let local_features = StrMap.map litlist_to_tab local_lits in
  let res = { global_features; local_features } in
  res

let ctx_ctx_init regex =
  let tab = make_tab [] regex in
  let () = Env.show_log "desymbolic" @@ fun _ -> pprint_head tab in
  tab
