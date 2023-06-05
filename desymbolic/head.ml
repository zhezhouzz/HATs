open Zzdatatype.Datatype
open Language
open Rty
open Sugar

module LitElem = struct
  type t = lit

  let compare = compare_lit
end

module PtyElem = struct
  type t = Rty.pty

  let compare = Rty.compare_pty
end

module LitMap = Map.Make (LitElem)
module PtyMap = Map.Make (PtyElem)

type 'a tab =
  | LitTab of { vs : string typed list; littab : 'a LitMap.t }
  | PtyTab of { ptytab : 'a PtyMap.t }
  | EmptyTab

type 'a head = {
  global_tab : 'a tab;
  ret_tab : 'a tab;
  local_tab : 'a tab StrMap.t;
}

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
    | PtyTab { ptytab = m } ->
        let pos_set =
          List.filter_map (fun (k, v) ->
              if v then Some (Rty.layout_pty k) else None)
          @@ List.of_seq @@ PtyMap.to_seq m
        in
        let neg_set =
          List.filter_map (fun (k, v) ->
              if not v then Some (spf "not %s" @@ Rty.layout_pty k) else None)
          @@ List.of_seq @@ PtyMap.to_seq m
        in
        Pp.printf "%s" (List.split_by "/\\" (fun x -> x) (pos_set @ neg_set))
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
    | PtyTab { ptytab = m } ->
        PtyMap.iter
          (fun pty idx -> Pp.printf "@{%i@}: %s, " idx (Rty.layout_pty pty))
          m
    | EmptyTab -> Pp.printf "%s" "Empty"
  in
  let () = Pp.printf "\n" in
  ()

let pprint_head { global_tab; local_tab; ret_tab } =
  let () = Pp.printf "[global_tab]:" in
  let () = pprint_tab global_tab in
  let () = Pp.printf "[ret_tab]:" in
  let () = pprint_tab ret_tab in
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
  (* let () = Pp.printf "[global_tab]:" in *)
  (* let () = pprint_tab (LitTab { vs = []; littab = m }) in *)
  let bv = NRegex.id_to_barr (LitMap.cardinal m) n in
  LitMap.map (fun idx -> bv.(idx)) m

let ptytab_i_to_b m n =
  let bv = NRegex.id_to_barr (PtyMap.cardinal m) n in
  PtyMap.map (fun idx -> bv.(idx)) m

let ptytab_get_nty m =
  let res =
    PtyMap.fold
      (fun pty _ nty ->
        match nty with Some _ -> nty | None -> Some (Rty.erase_pty pty))
      m None
  in
  match res with None -> _failatwith __FILE__ __LINE__ "die" | Some res -> res

let tab_i_to_b (tab : int tab) n =
  match tab with
  | EmptyTab -> EmptyTab
  | LitTab { littab = m; vs } -> LitTab { littab = littab_i_to_b m n; vs }
  | PtyTab { ptytab = m } -> PtyTab { ptytab = ptytab_i_to_b m n }

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
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

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
  | PtyTab _ -> _failatwith __FILE__ __LINE__ "die"

let tab_cardinal (tab : 'a tab) =
  match tab with
  | LitTab { littab = m; _ } -> LitMap.cardinal m
  | PtyTab { ptytab = m } -> PtyMap.cardinal m
  | EmptyTab -> 0

let head_cardinal { global_tab; ret_tab; local_tab } =
  tab_cardinal global_tab + tab_cardinal ret_tab
  + StrMap.fold (fun _ tab sum -> sum + tab_cardinal tab) local_tab 0

let tab_vs (tab : 'a tab) =
  match tab with
  | LitTab { vs; _ } ->
      let bindings =
        List.map (fun { x; ty } -> { px = x; pty = mk_top_pty ty }) vs
      in
      bindings
  | PtyTab _ -> []
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

let ptylist_to_tab l =
  let l = List.slow_rm_dup Rty.eq_pty l in
  if List.length l == 0 then EmptyTab
  else
    PtyTab
      {
        ptytab =
          List.fold_lefti (fun m idx lit -> PtyMap.add lit idx m) PtyMap.empty l;
      }

open Rty

let stat_max_minterms = ref 0
let stat_max_lits = ref 0
let record_max original n = if n > !original then original := n else ()

let num_lits { global_lits; global_pty; local_lits } =
  List.length global_lits + List.length global_pty
  + StrMap.fold (fun _ (_, tab) sum -> sum + List.length tab) local_lits 0

let make_tab regex =
  let g = gather_from_regex regex in
  let num_lits = num_lits g in
  let () = record_max stat_max_lits num_lits in
  let { global_lits; global_pty; local_lits } = g in
  let global_tab = litlist_to_tab ([], global_lits) in
  let local_tab = StrMap.map litlist_to_tab local_lits in
  let ret_tab = ptylist_to_tab global_pty in
  let res = { global_tab; ret_tab; local_tab } in
  res

let mk_minterm_ids n = List.init (NRegex.pow 2 n) (fun x -> x)
let mk_minterms_from_tab m = mk_minterm_ids (tab_cardinal m)

let mk_mts { global_tab; ret_tab; local_tab } =
  let local_m = StrMap.map mk_minterms_from_tab local_tab in
  let global_idxs = mk_minterms_from_tab global_tab in
  let ret_idxs = mk_minterms_from_tab ret_tab in
  let idxs = List.cross global_idxs ret_idxs in
  let m =
    List.fold_left (fun m idx -> GMap.add idx local_m m) GMap.empty idxs
  in
  m

let ctx_init regex =
  let tab = make_tab regex in
  let () = Env.show_debug_debug @@ fun _ -> pprint_head tab in
  let mts = mk_mts tab in
  let () = Env.show_debug_debug @@ fun _ -> NRegex.pprint_mts mts in
  (tab, mts)
