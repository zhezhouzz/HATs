include Baux
open Language
open Sugar
open Rty

(* open DT *)
open Zzdatatype.Datatype

type infer_ctx = { ftab : lit list }

let gathered_lit_to_atom_lit { local_lits; _ } =
  let local_lits =
    StrMap.map
      (fun (xs, lits) ->
        List.filter_map
          (fun lit ->
            let fv = L.fv_lit lit in
            let common =
              List.filter (fun x -> List.exists (String.equal x.x) fv) xs
            in
            match common with [ x ] -> Some (x, lit) | _ -> None)
          lits)
      local_lits
  in
  let lits = List.concat @@ StrMap.to_value_list local_lits in
  lits

let elrond verifier features fvtab =
  let rec loop () =
    match DT.pick_by_label fvtab DT.MayNeg with
    | Some fv ->
        let () =
          Env.show_log "elim_ghost" @@ fun _ ->
          Pp.printf "@{<bold>@{<orange> pick_maybepos: %s@}@}\n"
            (DT.layout_raw_fv fv)
        in
        let () = DT.label_as fvtab fv DT.Neg in
        let () =
          Env.show_log "elim_ghost" @@ fun _ ->
          Pp.printf "@{<bold>@{<yellow> fvtab@}@}\n";
          DT.pprint_fvtab features fvtab
        in
        let dt = DT.classify_hash_is_not_neg (Array.length features) fvtab in
        let prop = P.simpl @@ DT.to_prop features dt in
        if verifier prop then
          let () =
            Env.show_log "elim_ghost" @@ fun _ ->
            Pp.printf "@{<bold>@{<orange> label %s as - @}@}\n"
              (DT.layout_raw_fv fv)
          in
          loop ()
        else
          let () =
            Env.show_log "elim_ghost" @@ fun _ ->
            Pp.printf "@{<bold>@{<orange> label %s as + @}@}\n"
              (DT.layout_raw_fv fv)
          in
          (* let _ = failwith "end" in *)
          let () = DT.label_as fvtab fv DT.Pos in
          loop ()
    | None ->
        let dt = DT.classify_hash_is_not_neg (Array.length features) fvtab in
        let prop = P.simpl @@ DT.to_prop features dt in
        if verifier prop then Some prop else None
  in
  if verifier mk_true then
    let res = loop () in
    res
  else None

(* let candidate_to_prop ictx candidate = *)
(*   let l = List.map (fun idx -> List.nth ictx.ftab idx) candidate in *)
(*   match l with [] -> mk_false | _ -> Or l *)

(* let layout_solution ictx = function *)
(*   | PropFunc { candidate } -> *)
(*       let prop = candidate_to_prop ictx candidate in *)
(*       layout_prop prop *)

(* let layout_solution_raw _ = function *)
(*   | PropFunc { candidate } -> IntList.to_string candidate *)

(* let solution_instantiate ictx solution lits = *)
(*   match solution with *)
(*   | PropFunc { candidate } -> *)
(*       let prop = candidate_to_prop ictx candidate in *)
(*       (\* let ws = List.map (fun x -> x.x) ictx.ws in *\) *)
(*       let bindings = _safe_combine __FILE__ __LINE__ ictx.ws lits in *)
(*       List.fold_left *)
(*         (fun prop (y, z) -> subst_prop_id (y.x, z) prop) *)
(*         prop bindings *)

(* let mk_feature_tab lits = *)
(*   let rec aux lits = *)
(*     match lits with *)
(*     | [] -> [ [ Lit mk_lit_true ] ] *)
(*     | [ lit ] -> [ [ Lit lit ]; [ Not (Lit lit) ] ] *)
(*     | lit :: rs -> *)
(*         let res = aux rs in *)
(*         let res_t = List.map (fun conjs -> Lit lit :: conjs) res in *)
(*         let res_f = List.map (fun conjs -> Not (Lit lit) :: conjs) res in *)
(*         res_t @ res_f *)
(*   in *)
(*   let dnf = aux lits in *)
(*   List.map (fun conjs -> And conjs) dnf *)

let ghost_infer_one typectx (lpre : regex) (gvar : string Nt.typed)
    (rpre : regex) =
  let gathered = SRL.gather lpre in
  let lits = gathered_lit_to_atom_lit gathered in
  let () =
    Env.show_log "elim_ghost" @@ fun _ ->
    Printf.printf "lits:\n%s\n"
    @@ List.split_by "\n"
         (fun (x, lit) -> spf "%s:%s -> %s" x.x (layout x.ty) (layout_lit lit))
         lits
  in
  let type_safe_lits =
    List.filter_map
      (fun (x, lit) ->
        if Nt.eq x.ty gvar.ty then Some (L.subst_lit_id (x.x, v_name) lit)
        else None)
      lits
  in
  let () =
    Env.show_log "elim_ghost" @@ fun _ ->
    Printf.printf "type_safe_lits:\n%s\n"
    @@ List.split_by "\n" (fun lit -> spf "%s" (layout_lit lit)) type_safe_lits
  in
  let () = _failatwith __FILE__ __LINE__ "end" in
  let features = Array.of_list type_safe_lits in
  let fvtab = DT.init_fvtab features in
  let () = DT.pprint_fvtab features fvtab in
  (* let mk_solution x phi = (x,  #:: (mk_from_prop x.Nt.ty (fun _ -> phi)) in *)
  let verifier phi =
    let () =
      Env.show_log "elim_ghost" @@ fun _ ->
      Pp.printf "@{<bold>@{<yellow>verifier %s@}@}\n" (layout_prop phi)
    in
    let rpre = close_fv (gvar, phi) rpre in
    subtyping_srl_bool __FILE__ __LINE__ typectx (lpre, rpre)
  in
  let res = elrond verifier features fvtab in
  match res with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some phi -> mk_from_prop gvar.Nt.ty (fun _ -> phi)

let ghost_infer_aux typectx (lpre : regex) (gvars : string Nt.typed list)
    (rpre : regex) =
  match gvars with
  | [] -> []
  (* | [ x ] -> [ ghost_infer_one typectx lpre x rpre ] *)
  | [ x ] ->
      if true then [ mk_from_prop x.Nt.ty (fun _ -> mk_true) ]
      else [ ghost_infer_one typectx lpre x rpre ]
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

open TypedCoreEff

let mk_ctx_rty typectx gvars rtys hty =
  let bindings =
    List.map
      (fun (x, rty) -> { rx = x.x; rty })
      (_safe_combine __FILE__ __LINE__ gvars rtys)
  in
  let bindings, hty' =
    List.fold_left
      (fun (bindings, res) { rx; rty } ->
        let rx' = Rename.unique rx in
        let res = subst_hty_id (rx, rx') res in
        (bindings @ [ { rx = rx'; rty } ], res))
      ([], hty) bindings
  in
  let typectx' = typectx_new_to_rights typectx bindings in
  Some (typectx', hty_force_rty hty')

let ghost_infer typectx (lpre : regex) (args : value typed list) (rty : rty) =
  let gvars, rty = destruct_to_gbindings (Rty rty) in
  match gvars with
  | [] -> Some (typectx, hty_force_rty rty)
  | _ ->
      let () =
        Env.show_log "elim_ghost" @@ fun _ ->
        Printf.printf "[%s] %s\n"
          (List.split_by_comma (fun x -> spf "%s:%s" x.x (layout x.ty)) gvars)
          (layout_hty rty)
      in
      let ress =
        List.fold_left
          (fun hty v -> snd @@ Baux.app_v_func_rty v (hty_force_rty hty))
          rty args
      in
      let () =
        Env.show_log "elim_ghost" @@ fun _ ->
        Printf.printf "ress: %s\n" (layout_hty ress)
      in
      let rpre =
        match hty_to_pre_opt ress with
        | Some rpre -> rpre
        | None -> _failatwith __FILE__ __LINE__ "die"
      in
      let rtys = ghost_infer_aux typectx lpre gvars rpre in
      mk_ctx_rty typectx gvars rtys rty

let force_without_ghost typectx (rty : rty) (args : value typed list)
    (hty : hty) : (typectx * rty) option =
  let lpre = hty_to_pre_opt hty in
  match lpre with
  | Some lpre -> ghost_infer typectx lpre args rty
  | None ->
      let gvars, rty = destruct_to_gbindings (Rty rty) in
      let rtys = List.map (fun x -> Rty.mk_top x.ty) gvars in
      mk_ctx_rty typectx gvars rtys rty
