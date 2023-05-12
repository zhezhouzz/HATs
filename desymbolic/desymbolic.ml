include Head
open Zzdatatype.Datatype
open Language
open Rty.P
open Sugar

let minterm_to_op_model { global_tab; local_tab }
    NRegex.{ op; global_embedding; local_embedding } =
  let global_m = tab_i_to_b global_tab global_embedding in
  let m = StrMap.find "minterm_to_op_model" local_tab op in
  let local_m = tab_i_to_b m local_embedding in
  (global_m, local_m)

let model_verify_bool sub_pty_bool (global_m, local_m) =
  match local_m with
  | EmptyTab | LitTab _ ->
      let m = merge_global_to_local global_m local_m in
      let rhs_pty = Rty.mk_unit_under_pty_from_prop @@ tab_to_prop m in
      let lhs_pty = Rty.mk_unit_under_pty_from_prop mk_false in
      (* let () = *)
      (*   Pp.printf "%s <: @{<bold>%s@}\n" (Rty.layout_pty lhs_pty) *)
      (*     (Rty.layout_pty rhs_pty) *)
      (* in *)
      not (sub_pty_bool [] (lhs_pty, rhs_pty))
  | PtyTab local_m ->
      let ctxurty = Rty.mk_unit_under_rty_from_prop @@ tab_to_prop global_m in
      let binding = Rty.((Rename.unique "a") #: ctxurty) in
      let pos_set =
        List.filter_map (fun (k, v) -> if v then Some k else None)
        @@ List.of_seq @@ PtyMap.to_seq local_m
      in
      let neg_set =
        List.filter_map (fun (k, v) -> if not v then Some k else None)
        @@ List.of_seq @@ PtyMap.to_seq local_m
      in
      (* let () = *)
      (*   Printf.printf "pos_set: %s\n" *)
      (*   @@ List.split_by_comma Rty.layout_pty pos_set *)
      (* in *)
      (* let () = *)
      (*   Printf.printf "neg_set: %s\n" *)
      (*   @@ List.split_by_comma Rty.layout_pty neg_set *)
      (* in *)
      let lhs_pty, rhs_pty =
        match (pos_set, neg_set) with
        (* NOTE: when pos_set (neg_set) is empty, it is equal to the top (bottom) element in the subtyping lattice *)
        (* TODO: It is a nice feature that is consistent with the normal logic, why not move it into the conj/conj of types? *)
        | [], _ ->
            let lhs_pty = Auxtyping.conj_ptys neg_set in
            let rhs_pty = Rty.(mk_top_pty @@ erase_pty lhs_pty) in
            (lhs_pty, rhs_pty)
        | _, [] ->
            let rhs_pty = Auxtyping.conj_ptys pos_set in
            let lhs_pty = Rty.(mk_bot_pty @@ erase_pty rhs_pty) in
            (lhs_pty, rhs_pty)
        | _, _ ->
            let lhs_pty = Auxtyping.disj_ptys neg_set in
            let rhs_pty = Auxtyping.conj_ptys pos_set in
            (lhs_pty, rhs_pty)
      in
      (* let () = *)
      (*   Pp.printf "%s |- %s <: @{<bold>%s@}\n" *)
      (*     (Rty.layout_typed (fun x -> x) binding) *)
      (*     (Rty.layout_pty lhs_pty) (Rty.layout_pty rhs_pty) *)
      (* in *)
      (* let () = failwith "end" in *)
      let b = not (sub_pty_bool [ binding ] (lhs_pty, rhs_pty)) in
      (* let () = Pp.printf "@{<bold>if_valid: %b@}\n" b in *)
      b

let minterm_verify_bool sub_pty_bool ctx mt =
  let model = minterm_to_op_model ctx mt in
  model_verify_bool sub_pty_bool model

let op_models (global_m, local_m) prop =
  let m = merge_global_to_local global_m local_m in
  let rec aux prop =
    match prop with
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

let ret_models local_m pty =
  let local_m =
    match local_m with
    | LitTab _ | EmptyTab -> _failatwith __FILE__ __LINE__ "die"
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

let models_event ctx mt = function
  | RetEvent pty ->
      if String.equal mt.NRegex.op ret_name then
        let _, local_m = minterm_to_op_model ctx mt in
        ret_models local_m pty
      else false
  | EffEvent { op; phi; _ } ->
      if String.equal mt.NRegex.op op then
        let global_m, local_m = minterm_to_op_model ctx mt in
        op_models (global_m, local_m) phi
      else false

let desymbolic_sevent ctx mts se =
  let op = se_get_op se in
  let mts =
    NRegex.mts_fold_on_op op
      (fun mt res ->
        if models_event ctx mt se then NRegex.Minterm mt :: res else res)
      mts []
  in
  NRegex.Union mts

let desymbolic ctx mts regex =
  let rec aux regex =
    match regex with
    | EpsilonA -> NRegex.Epslion
    | EventA se -> desymbolic_sevent ctx mts se
    | LorA (t1, t2) -> NRegex.Union (List.map aux [ t1; t2 ])
    | LandA (t1, t2) -> NRegex.Intersect (List.map aux [ t1; t2 ])
    | SeqA (t1, t2) -> NRegex.Concat (List.map aux [ t1; t2 ])
    | StarA t -> NRegex.Star (aux t)
    | ExistsA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux regex
