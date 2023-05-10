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

type lit_map = { lit_to_idx : int LitMap.t; idx_to_lit : lit IntMap.t }
type pty_map = { pty_to_idx : int PtyMap.t; idx_to_pty : Rty.pty IntMap.t }
type head = { optab : lit_map StrMap.t; rettab : pty_map }
type mts = { opmts : int list StrMap.t; retmts : int list }
(* type mt = { op : string; n : int } *)

let rec id_to_bl len n res =
  if len == 0 then res
  else
    let x = 0 == n mod 2 in
    id_to_bl (len - 1) (n / 2) (x :: res)

let id_to_barr len n = Array.of_list @@ id_to_bl len n []

let mk_lit_tab mt_map n =
  let len = LitMap.cardinal mt_map.lit_to_idx in
  let arr = id_to_barr len n in
  LitMap.map (fun i -> arr.(i)) mt_map.lit_to_idx

let mk_pty_tab mt_map n =
  let len = PtyMap.cardinal mt_map.pty_to_idx in
  let arr = id_to_barr len n in
  PtyMap.map (fun i -> arr.(i)) mt_map.pty_to_idx

open Sugar

let op_models_ m n prop =
  let m = mk_lit_tab m n in
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

let ret_models_ m n pty =
  let m = mk_pty_tab m n in
  PtyMap.find pty m

let minterm_to_qualifier { optab; _ } (op, n) =
  let mt_map = StrMap.find "minterm die" optab op in
  let len = LitMap.cardinal mt_map.lit_to_idx in
  let l = id_to_bl len n [] in
  let props =
    List.mapi
      (fun i b ->
        let lit = Lit (IntMap.find "minterm die" mt_map.idx_to_lit i) in
        if b then lit else Not lit)
      l
  in
  And props

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
      let b = pow a (n / 2) in
      b * b * if n mod 2 = 0 then 1 else a

open Rty

let minterm_to_cty ctx (op, n) =
  match op with
  | "Ret" -> _failatwith __FILE__ __LINE__ "die"
  | _ ->
      BasePty
        {
          ou = Under;
          cty =
            {
              v = Nt.{ x = "v"; ty = Ty_unit };
              phi = minterm_to_qualifier ctx (op, n);
            };
        }

let minterm_to_ptys ctx (op, n) =
  match op with
  | "Ret" ->
      let len = IntMap.cardinal ctx.rettab.idx_to_pty in
      let l = id_to_bl len n [] in
      let pos_set =
        List.filter_mapi
          (fun idx b ->
            if b then
              Some (IntMap.find "minterm_to_ptys" ctx.rettab.idx_to_pty idx)
            else None)
          l
      in
      let neg_set =
        List.filter_mapi
          (fun idx b ->
            if not b then
              Some (IntMap.find "minterm_to_ptys" ctx.rettab.idx_to_pty idx)
            else None)
          l
      in
      (pos_set, neg_set)
  | _ -> _failatwith __FILE__ __LINE__ "die"

let ret_name = "Ret"

let models_event { optab; rettab } { opmts; retmts } = function
  | RetEvent pty ->
      let retmts = List.filter (fun n -> ret_models_ rettab n pty) retmts in
      List.map (fun n -> (ret_name, n)) retmts
  | EffEvent { op; phi; _ } ->
      let tab = StrMap.find "models die" optab op in
      let opmts = StrMap.find "models die" opmts op in
      let opmts = List.filter (fun n -> op_models_ tab n phi) opmts in
      List.map (fun n -> (op, n)) opmts

let mk_rev_optab m =
  LitMap.fold (fun lit idx m -> IntMap.add idx lit m) m IntMap.empty

let mk_rev_rettab m =
  PtyMap.fold (fun lit idx m -> IntMap.add idx lit m) m IntMap.empty

let make_head regex =
  let optab = get_lits_from_regex regex in
  let optab =
    StrMap.map
      (fun l ->
        let m =
          List.fold_lefti (fun m idx lit -> LitMap.add lit idx m) LitMap.empty l
        in
        { lit_to_idx = m; idx_to_lit = mk_rev_optab m })
      optab
  in
  let rettab = get_ptys_from_regex regex in
  let m =
    List.fold_lefti (fun m idx lit -> PtyMap.add lit idx m) PtyMap.empty rettab
  in
  let rettab = { pty_to_idx = m; idx_to_pty = mk_rev_rettab m } in
  { optab; rettab }

let mk_minterm_ids n = List.init (pow 2 n) (fun x -> x)

let mk_mts { optab; rettab } =
  let opmts =
    StrMap.map (fun x -> mk_minterm_ids (LitMap.cardinal x.lit_to_idx)) optab
  in
  let retmts = mk_minterm_ids (PtyMap.cardinal rettab.pty_to_idx) in
  { opmts; retmts }

let minterm_init regex =
  let head = make_head regex in
  (head, mk_mts head)

(* let filter_optab f optab opmts = *)
(*   StrMap.mapi (fun op mts -> *)
(*       minterm_to_cty ctx (op, n) *)
(*       List.filter (fun mt -> f op mt) mts *)
(*     ) ctx.opmts *)

let desymbolic tab mts regex =
  let rec aux regex =
    match regex with
    | VarA _ -> _failatwith __FILE__ __LINE__ "die"
    | EpsilonA -> NRegex.Epslion
    | EventA se ->
        let mts = models_event tab mts se in
        let mts = List.map (fun (op, n) -> NRegex.Minterm (op, n)) mts in
        NRegex.Union mts
    | LorA (t1, t2) -> NRegex.Union (List.map aux [ t1; t2 ])
    | SeqA (t1, t2) -> NRegex.Concat (List.map aux [ t1; t2 ])
    | StarA t -> NRegex.Star (aux t)
    | ExistsA _ -> _failatwith __FILE__ __LINE__ "die"
    | RecA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux regex
