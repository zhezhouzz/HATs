open Zzdatatype.Datatype
open Language
open Language.Rty.P
open Sugar

module LitElem = struct
  type t = lit

  let compare = compare_lit
end

module LitMap = Map.Make (LitElem)
open Rty

type 'a tab =
  | LitTab of { vs : string typed list; littab : 'a LitMap.t }
  | EmptyTab

type 'a head = { global_tab : 'a tab; local_tab : 'a tab StrMap.t }

let pprint_bool_tab m =
  let () =
    match m with
    | LitTab { littab = m; _ } ->
        let pos_set =
          List.filter_map (fun (k, v) -> if v then Some (Lit k) else None)
          @@ List.of_seq @@ LitMap.to_seq m
        in
        let neg_set =
          List.filter_map (fun (k, v) ->
              if not v then Some (Not (Lit k)) else None)
          @@ List.of_seq @@ LitMap.to_seq m
        in
        Pp.printf "%s" (Rty.layout_prop (And (pos_set @ neg_set)))
    | EmptyTab -> Pp.printf "true"
  in
  let () = Pp.printf "\n" in
  ()

let pprint_tab m =
  let () =
    match m with
    | LitTab { littab = m; _ } ->
        LitMap.iter
          (fun lit idx -> Pp.printf "@{%i@}: %s, " idx (Rty.layout_lit lit))
          m
    | EmptyTab -> Pp.printf "%s" "Empty"
  in
  let () = Pp.printf "\n" in
  ()

let pprint_head { global_tab; local_tab } =
  let () = Pp.printf "[global_tab]:" in
  let () = pprint_tab global_tab in
  let () = Pp.printf "[local_tab]:\n" in
  let () =
    StrMap.iter
      (fun op m ->
        let () = Pp.printf "[%s]: " op in
        pprint_tab m)
      local_tab
  in
  ()

let littab_i_to_b m n =
  let bv = NRegex.id_to_barr (LitMap.cardinal m) n in
  LitMap.map (fun idx -> bv.(idx)) m

let tab_i_to_b (tab : int tab) n =
  match tab with
  | EmptyTab -> EmptyTab
  | LitTab { littab = m; vs } -> LitTab { littab = littab_i_to_b m n; vs }

let merge_global_to_local global_m local_m =
  match (global_m, local_m) with
  | EmptyTab, _ -> local_m
  | LitTab _, EmptyTab -> global_m
  | LitTab { littab = m1; vs = vs1 }, LitTab { littab = m2; vs = vs2 } ->
      LitTab
        {
          littab = LitMap.add_seq (LitMap.to_seq m1) m2;
          vs = List.slow_rm_dup (fun x y -> String.equal x.x y.x) vs1 @ vs2;
        }

let tab_models_lit m lit =
  match m with
  | LitTab { littab = m; _ } -> LitMap.find lit m
  | _ -> _failatwith __FILE__ __LINE__ "die"

let tab_to_prop = function
  | EmptyTab -> mk_true
  | LitTab { littab = m; _ } ->
      let l =
        LitMap.fold
          (fun lit b m -> if b then Lit lit :: m else Not (Lit lit) :: m)
          m []
      in
      smart_and l

let tab_cardinal (tab : 'a tab) =
  match tab with LitTab { littab = m; _ } -> LitMap.cardinal m | EmptyTab -> 0

let head_cardinal { global_tab; local_tab } =
  tab_cardinal global_tab
  + StrMap.fold (fun _ tab sum -> sum + tab_cardinal tab) local_tab 0

let tab_vs (tab : 'a tab) =
  match tab with
  | LitTab { vs; _ } ->
      let bindings =
        List.map (fun { x; ty } -> Rty.{ rx = x; rty = mk_top ty }) vs
      in
      bindings
  | EmptyTab -> []

let litlist_to_tab (vs, l) =
  let l = List.slow_rm_dup eq_lit l in
  if List.length l == 0 then EmptyTab
  else
    LitTab
      {
        littab =
          List.fold_lefti (fun m idx lit -> LitMap.add lit idx m) LitMap.empty l;
        vs;
      }

(* let stat_max_minterms = ref 0 *)
(* let stat_max_lits = ref 0 *)
(* let record_max original n = if n > !original then original := n else () *)

(* let num_lits { global_lits; global_rty; local_lits } = *)
(*   List.length global_lits + List.length global_rty *)
(*   + StrMap.fold (fun _ (_, tab) sum -> sum + List.length tab) local_lits 0 *)

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
  (* let () = *)
  (*   Printf.printf "global_args: %s\n" *)
  (*     (List.split_by_comma (fun x -> layout_lit x.x) global_args) *)
  (* in *)
  let euf_constraints = build_euf global_args in
  let global_lits =
    List.slow_rm_dup (fun x y -> L.eq_lit x y)
    @@ global_lits @ euf_constraints @ addtional_global_lits
  in
  let global_tab = litlist_to_tab ([], global_lits) in
  let local_tab = StrMap.map litlist_to_tab local_lits in
  let res = { global_tab; local_tab } in
  res

let mk_minterm_ids n = List.init (NRegex.pow 2 n) (fun x -> x)
let mk_minterms_from_tab m = mk_minterm_ids (tab_cardinal m)

let mk_mts { global_tab; local_tab } =
  let local_m = StrMap.map mk_minterms_from_tab local_tab in
  let global_idxs = mk_minterms_from_tab global_tab in
  let idxs = global_idxs in
  let m =
    List.fold_left (fun m idx -> IntMap.add idx local_m m) IntMap.empty idxs
  in
  m

(* let ctx_init regex = *)
(*   let tab = make_tab [] regex in *)
(*   let () = Env.show_log "desymbolic" @@ fun _ -> pprint_head tab in *)
(*   let mts = mk_mts tab in *)
(*   let () = Env.show_log "desymbolic" @@ fun _ -> NRegex.pprint_mts mts in *)
(*   (tab, mts) *)

let ctx_ctx_init _ regex =
  (* let global_vars = *)
  (*   List.filter_map *)
  (*     (fun (x, rty) -> *)
  (*       match erase_rty rty with *)
  (*       | Nt.Ty_arrow _ | Nt.Ty_unit | Nt.Ty_bool -> None *)
  (*       | ty -> Some Nt.{ x = AVar x; ty }) *)
  (*     rctx *)
  (* in *)
  (* let () = *)
  (*   Env.show_log "subtyping" @@ fun _ -> *)
  (*   Printf.printf "global_vars:\n%s\n" *)
  (*   @@ List.split_by "\n" *)
  (*        (fun x -> spf "%s" (layout_typed layout_lit x)) *)
  (*        global_vars *)
  (* in *)
  (* let euf_constraints = build_euf global_vars in *)
  (* let () = *)
  (*   Env.show_log "subtyping" @@ fun _ -> *)
  (*   Printf.printf "euf_constraints:\n%s\n" *)
  (*   @@ List.split_by "\n" (fun x -> spf "%s" (layout_lit x)) euf_constraints *)
  (* in *)
  let tab = make_tab [] regex in
  let () = Env.show_log "desymbolic" @@ fun _ -> pprint_head tab in
  let mts = mk_mts tab in
  let () = Env.show_log "desymbolic" @@ fun _ -> NRegex.pprint_mts mts in
  (tab, mts)
