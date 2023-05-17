open Zzdatatype.Datatype
open Language
open Rty.P
open Sugar

module LitElem = struct
  type t = lit

  let compare = compare
end

module PtyElem = struct
  type t = Rty.pty

  let compare = Rty.compare_pty
end

module LitMap = Map.Make (LitElem)
module PtyMap = Map.Make (PtyElem)

type 'a tab = LitTab of 'a LitMap.t | PtyTab of 'a PtyMap.t | EmptyTab
type 'a head = { global_tab : 'a tab; local_tab : 'a tab StrMap.t }

let pprint_bool_tab m =
  let () =
    match m with
    | LitTab m ->
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
    | PtyTab m ->
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
    | LitTab m ->
        LitMap.iter
          (fun lit idx -> Pp.printf "@{%i@}: %s, " idx (Rty.layout_lit lit))
          m
    | PtyTab m ->
        PtyMap.iter
          (fun pty idx -> Pp.printf "@{%i@}: %s, " idx (Rty.layout_pty pty))
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
  | LitTab m -> LitTab (littab_i_to_b m n)
  | PtyTab m -> PtyTab (ptytab_i_to_b m n)

let merge_global_to_local global_m local_m =
  match (global_m, local_m) with
  | EmptyTab, _ -> local_m
  | LitTab _, EmptyTab -> global_m
  | LitTab m1, LitTab m2 -> LitTab (LitMap.add_seq (LitMap.to_seq m1) m2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

let tab_models_lit m lit =
  match m with
  | LitTab m -> LitMap.find lit m
  | _ -> _failatwith __FILE__ __LINE__ "die"

let tab_to_prop = function
  | EmptyTab -> mk_true
  | LitTab m ->
      let l =
        LitMap.fold
          (fun lit b m -> if b then Lit lit :: m else Not (Lit lit) :: m)
          m []
      in
      smart_and l
  | PtyTab _ -> _failatwith __FILE__ __LINE__ "die"

let tab_cardinal (tab : 'a tab) =
  match tab with
  | LitTab m -> LitMap.cardinal m
  | PtyTab m -> PtyMap.cardinal m
  | EmptyTab -> 0

let litlist_to_tab l =
  if List.length l == 0 then EmptyTab
  else
    LitTab
      (List.fold_lefti (fun m idx lit -> LitMap.add lit idx m) LitMap.empty l)

let ptylist_to_tab l =
  if List.length l == 0 then EmptyTab
  else
    PtyTab
      (List.fold_lefti (fun m idx lit -> PtyMap.add lit idx m) PtyMap.empty l)

open Rty

let make_tab regex =
  let { global_lits; global_pty; local_lits } = gather_from_regex regex in
  let global_tab = litlist_to_tab global_lits in
  let local_lits_map = StrMap.map litlist_to_tab local_lits in
  let ret_enrty = ptylist_to_tab global_pty in
  let local_tab = StrMap.add ret_name ret_enrty local_lits_map in
  { global_tab; local_tab }

let mk_minterm_ids n = List.init (NRegex.pow 2 n) (fun x -> x)
let mk_minterms_from_tab m = mk_minterm_ids (tab_cardinal m)

let mk_mts { global_tab; local_tab } =
  let local_m = StrMap.map mk_minterms_from_tab local_tab in
  let global_idxs = mk_minterms_from_tab global_tab in
  let m =
    List.fold_left
      (fun m global_idx -> IntMap.add global_idx local_m m)
      IntMap.empty global_idxs
  in
  m

let ctx_init regex =
  let tab = make_tab regex in
  let () = pprint_head tab in
  let mts = mk_mts tab in
  let () = NRegex.pprint_mts mts in
  (tab, mts)
