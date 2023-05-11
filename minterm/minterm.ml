open Zzdatatype.Datatype
open Language
open Rty.P

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

type 'a tab = LitTab of 'a LitMap.t | PtyTab of 'a PtyMap.t
type 'a head = { global_tab : 'a LitMap.t; local_tab : 'a tab StrMap.t }

let littab_i_to_b m n =
  let bv = NRegex.id_to_barr (LitMap.cardinal m) n in
  LitMap.map (fun idx -> bv.(idx)) m

let ptytab_i_to_b m n =
  let bv = NRegex.id_to_barr (PtyMap.cardinal m) n in
  PtyMap.map (fun idx -> bv.(idx)) m

let tab_i_to_b (tab : int tab) n =
  match tab with
  | LitTab m -> LitTab (littab_i_to_b m n)
  | PtyTab m -> PtyTab (ptytab_i_to_b m n)

let minterm_to_op_model { global_tab; local_tab }
    NRegex.{ op; gobal_embedding; local_embedding } =
  let gobal_m = littab_i_to_b global_tab gobal_embedding in
  let m = StrMap.find "minterm_to_op_model" local_tab op in
  let local_m = tab_i_to_b m local_embedding in
  (gobal_m, local_m)

open Sugar

let model_to_qualifier (gobal_m, local_m) =
  match local_m with
  | LitTab local_m ->
      let m = LitMap.add_seq (LitMap.to_seq gobal_m) local_m in
      let l =
        LitMap.fold
          (fun lit b m -> if b then Lit lit :: m else Not (Lit lit) :: m)
          m []
      in
      let urty = Rty.mk_unit_under_rty_from_prop @@ And l in
      ([], (Rty.mk_unit_under_rty_from_prop mk_false, urty))
  | PtyTab local_m ->
      let l =
        LitMap.fold
          (fun lit b m -> if b then Lit lit :: m else Not (Lit lit) :: m)
          gobal_m []
      in
      let ctxurty = Rty.mk_unit_under_rty_from_prop @@ And l in
      let pos_set =
        List.filter_map (fun (k, v) -> if v then Some (Rty.Pty k) else None)
        @@ List.of_seq @@ PtyMap.to_seq local_m
      in
      let neg_set =
        List.filter_map (fun (k, v) -> if not v then Some (Rty.Pty k) else None)
        @@ List.of_seq @@ PtyMap.to_seq local_m
      in
      ([ ctxurty ], (Auxtyping.merge_rtys pos_set, Auxtyping.merge_rtys neg_set))

let op_models (gobal_m, local_m) prop =
  let local_m =
    match local_m with
    | LitTab m -> m
    | PtyTab _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let m = LitMap.add_seq (LitMap.to_seq gobal_m) local_m in
  let rec aux prop =
    match prop with
    | Lit lit -> LitMap.find lit m
    | Implies (a, b) -> (not (aux a)) || aux b
    | Ite (a, b, c) -> if aux a then aux b else aux c
    | Not a -> not (aux a)
    | And es -> List.for_all aux es
    | Or es -> List.exists aux es
    | Iff (a, b) -> aux (Implies (a, b)) && aux (Implies (b, a))
    | Forall _ | Exists _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux prop

let ret_models local_m pty =
  let local_m =
    match local_m with
    | LitTab _ -> _failatwith __FILE__ __LINE__ "die"
    | PtyTab m -> m
  in
  PtyMap.find pty local_m

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

let ret_name = "Ret"

let models_event ctx mt = function
  | RetEvent pty ->
      if String.equal mt.NRegex.op ret_name then
        let _, local_m = minterm_to_op_model ctx mt in
        ret_models local_m pty
      else false
  | EffEvent { op; phi; _ } ->
      if String.equal mt.NRegex.op op then
        let gobal_m, local_m = minterm_to_op_model ctx mt in
        op_models (gobal_m, local_m) phi
      else false

let desymbolic ctx mts regex =
  let rec aux regex =
    match regex with
    | VarA _ -> _failatwith __FILE__ __LINE__ "die"
    | EpsilonA -> NRegex.Epslion
    | EventA se ->
        let mts =
          NRegex.fold_mts
            (fun mt res ->
              if models_event ctx mt se then NRegex.Minterm mt :: res else res)
            mts []
        in
        NRegex.Union mts
    | LorA (t1, t2) -> NRegex.Union (List.map aux [ t1; t2 ])
    | SeqA (t1, t2) -> NRegex.Concat (List.map aux [ t1; t2 ])
    | StarA t -> NRegex.Star (aux t)
    | ExistsA _ -> _failatwith __FILE__ __LINE__ "die"
    | RecA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux regex

let litlist_to_tab l =
  List.fold_lefti (fun m idx lit -> LitMap.add lit idx m) LitMap.empty l

let ptylist_to_tab l =
  List.fold_lefti (fun m idx lit -> PtyMap.add lit idx m) PtyMap.empty l

let make_tab regex =
  let global_lits, local_lits_map = get_lits_from_regex regex in
  let global_m = litlist_to_tab global_lits in
  let local_lits_map =
    StrMap.map (fun l -> LitTab (litlist_to_tab l)) local_lits_map
  in
  let ptys = get_ptys_from_regex regex in
  let ret_enrty = PtyTab (ptylist_to_tab ptys) in
  let local_m = StrMap.add ret_name ret_enrty local_lits_map in
  { global_m; local_m }

let mk_minterm_ids n = List.init (NRegex.pow 2 n) (fun x -> x)

let mk_mts { global_m; local_m } =
  let local_m = StrMap.map (fun m ->
      let ids = 
    )
  IntMap.from_kv_list @@ List.init (LitMap.cardinal global) ()
  let opmts =
    StrMap.map (fun x -> mk_minterm_ids (LitMap.cardinal x.lit_to_idx)) optab
  in
  let retmts = mk_minterm_ids (PtyMap.cardinal rettab.pty_to_idx) in
  { opmts; retmts }

let minterm_init regex =
  let tab = make_tab regex in
  (tab, mk_mts tab)

(* let filter_optab f optab opmts = *)
(*   StrMap.mapi (fun op mts -> *)
(*       minterm_to_cty ctx (op, n) *)
(*       List.filter (fun mt -> f op mt) mts *)
(*     ) ctx.opmts *)
