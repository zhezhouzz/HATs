open Language
module RCtx = RTypectx
module P = Rty.P
module ECtx = Eqctx
open Rty
open Sugar
open Zzdatatype.Datatype

type pctx = {
  eqctx : ECtx.ctx;
  gamma : RCtx.ctx;
  actx : Alpha.tmp_under_ctx;
  check : RCtx.ctx -> prop -> bool;
}

let check_prop_valid { gamma; actx; check; _ } phi =
  let actx = Alpha.choose_need actx @@ fv_prop phi in
  let gamma = gamma @ Alpha.to_rctx actx in
  check gamma phi

let cond_to_cond_prop eqconds =
  P.(smart_and (List.map (fun lit -> Lit lit) eqconds))

let reduction_none_on_op pctx pre se2 =
  let op2, vs2, phi2 = se_force_op se2 in
  let args2 = List.map (fun x -> find_lit_assignment_from_prop phi2 x) vs2 in
  let res = ECtx.find_none_ret_rules pctx.eqctx (op2, args2) in
  let res =
    List.filter_map
      (fun (res, cond) ->
        let () =
          Printf.printf "res: %s; cond: %s\n" (ECtx.layout_ret_res res)
            (List.split_by_comma layout_lit cond)
        in
        let cond = cond_to_cond_prop cond in
        let prop = smart_and [ pre; cond ] in
        let () =
          Printf.printf "pre: %s; prop: %s\n" (layout_prop pre)
            (layout_prop prop)
        in
        if check_prop_valid pctx prop then Some (cond, res) else None)
      res
  in
  let res1 =
    List.filter_map
      (fun (cond, x) ->
        match x with ECtx.Drop -> Some cond | ECtx.RetResLit _ -> None)
      res
  in
  let res2 =
    List.filter_map
      (fun (cond, x) ->
        match x with ECtx.Drop -> None | ECtx.RetResLit lit -> Some (cond, lit))
      res
  in
  let force_at_most_one res1 =
    if List.length res1 <= 1 then res1 else _failatwith __FILE__ __LINE__ "die"
    (* match res1 with *)
    (* | [ res1 ] -> Some res1 *)
    (* | [] -> None *)
    (* | _ -> _failatwith __FILE__ __LINE__ "die" *)
  in
  let res1 = force_at_most_one res1 in
  let res2 = force_at_most_one res2 in
  (res1, res2)

let reduction_single_on_op pctx pre se1 se2 =
  let op1, vs1, phi1 = se_force_op se1 in
  let op2, vs2, phi2 = se_force_op se2 in
  let args1 = List.map (fun x -> find_lit_assignment_from_prop phi1 x) vs1 in
  let args2 = List.map (fun x -> find_lit_assignment_from_prop phi2 x) vs2 in
  let res = ECtx.find_ret_rules pctx.eqctx (op1, args1) (op2, args2) in
  let res =
    List.filter_map
      (fun (res, cond) ->
        let cond = cond_to_cond_prop cond in
        if check_prop_valid pctx (smart_and [ pre; cond ]) then Some (cond, res)
        else None)
      res
  in
  let res1 =
    List.filter_map
      (fun (cond, x) ->
        match x with ECtx.Drop -> Some cond | ECtx.RetResLit _ -> None)
      res
  in
  let res2 =
    List.filter_map
      (fun (cond, x) ->
        match x with ECtx.Drop -> None | ECtx.RetResLit lit -> Some (cond, lit))
      res
  in
  let force_at_most_one res1 =
    if List.length res1 <= 1 then res1 else _failatwith __FILE__ __LINE__ "die"
    (* match res1 with *)
    (* | [ res1 ] -> Some res1 *)
    (* | [] -> None *)
    (* | _ -> _failatwith __FILE__ __LINE__ "die" *)
  in
  let res1 = force_at_most_one res1 in
  let res2 = force_at_most_one res2 in
  (res1, res2)
(* let conds = *)
(*   List.filter_map *)
(*     (fun (cond, v_opt) -> *)
(*       match v_opt with *)
(*       | None -> *)
(*           if check_prop_valid pctx (And [ pre; cond ]) then Some cond *)
(*           else None *)
(*       | Some _ -> None) *)
(*     cases *)
(* in *)
(* let rets = *)
(*   List.filter_map *)
(*     (fun (cond, v_opt) -> *)
(*       match v_opt with *)
(*       | None -> None *)
(*       | Some v -> *)
(*           if check_prop_valid pctx (And [ pre; cond ]) then *)
(*             let phi = mk_prop_var_eq_lit x v in *)
(*             Some phi *)
(*           else None) *)
(*     cases *)
(* in *)
(* let phi = *)
(*   match rets with *)
(*   | [] -> None *)
(*   | [ res ] -> Some res *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
(* in *)
(* let cond = *)
(*   match conds with *)
(*   | [] -> mk_false *)
(*   | [ cond ] -> cond *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
(* in *)
(* (cond, phi) *)

let reduction_drop_on_op pctx se regex : prop =
  let rec aux topcond regex =
    match regex with
    | EpsilonA -> topcond
    | SeqA (t1, t2) -> aux (aux topcond t1) t2
    | EventA se1 -> (
        let drop, _ = reduction_single_on_op pctx topcond se1 se in
        match drop with
        | [] -> mk_false
        | [ cond ] -> smart_and [ topcond; cond ]
        | _ -> _failatwith __FILE__ __LINE__ "die")
    | LorA (t1, t2) ->
        let cond1 = aux topcond t1 in
        let cond2 = aux topcond t2 in
        smart_or [ cond1; cond2 ]
    | LandA (t1, t2) ->
        let cond1 = aux topcond t1 in
        let cond2 = aux topcond t2 in
        smart_and [ cond1; cond2 ]
    | StarA t -> aux topcond (LorA (LorA (EpsilonA, t), SeqA (t, t)))
    | SigmaA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux mk_true regex

let reduction_on_op pctx se regex (x, phi_k) =
  let rec aux topcond regex =
    match regex with
    | EpsilonA -> None
    | SeqA (t1, t2) ->
        let* res1 = aux topcond t1 in
        let cond1 = reduction_drop_on_op pctx se t1 in
        let* res2 = aux (smart_and [ cond1; topcond ]) t2 in
        Some (LorA (SeqA (res1, t2), res2))
    | EventA se1 -> (
        let _, res = reduction_single_on_op pctx topcond se1 se in
        match res with
        | [ (cond, lit) ] ->
            let phi = mk_prop_var_eq_lit x lit in
            let phi = smart_and [ topcond; cond; phi ] in
            Some (SeqA (phi_k phi, EventA se))
        | [] -> None
        | _ -> _failatwith __FILE__ __LINE__ "die")
    | LorA (t1, t2) ->
        let* r1 = aux topcond t1 in
        let* r2 = aux topcond t2 in
        Some (LorA (r1, r2))
    | LandA (t1, t2) ->
        let* r1 = aux topcond t1 in
        let* r2 = aux topcond t2 in
        Some (LandA (r1, r2))
    | StarA t -> aux topcond (LorA (LorA (EpsilonA, t), SeqA (t, t)))
    | SigmaA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let _, res = reduction_none_on_op pctx mk_true se in
  match res with
  | [ (cond, lit) ] ->
      let phi = mk_prop_var_eq_lit x lit in
      let phi = smart_and [ cond; phi ] in
      SeqA (phi_k phi, SeqA (EventA se, regex))
  | [] -> (
      let res = aux mk_true regex in
      match res with None -> _failatwith __FILE__ __LINE__ "die" | Some r -> r)
  | _ -> _failatwith __FILE__ __LINE__ "die"

(* let reduction_on_op pctx se regex (x, phi_k) = *)
(*   (\* let construct_aux (x, phi_k) (cond, res) = *\) *)
(*   (\*   match res with *\) *)
(*   (\*   | ECtx.RetResLit lit -> *\) *)
(*   (\*     let phi = mk_prop_var_eq_lit x lit in *\) *)
(*   (\*     let phi = And [topcond; cond; phi] in *\) *)
(*   (\*     RFinished (phi_k phi) *\) *)
(*   (\*   | ECtx.Drop -> *\) *)
(*   (\*     let cond = And [topcond; cond] in *\) *)
(*   (\*     TRContinue cond *\) *)
(*   (\* in *\) *)
(*   let rec aux  regex = *)
(*     match regex with *)
(*     | EpsilonA -> (mk_true, phi_k cond) *)
(*     | SeqA (t1, t2) -> *)
(*         let cond1, res1 = aux cond t1 in *)
(*         let res1 = SeqA (res1, t2) in *)
(*         let cond2, res2 = aux (And [ cond1; cond ]) t2 in *)
(*         (cond2, LorA (res1, res2)) *)
(*     | EventA se1 -> ( *)
(*         let res = reduction_single_on_op pctx cond se1 se in *)
(*         let res = List.map (fun (cd, res) -> *)
(*             match res with *)
(*             | ECtx.RetResLit lit -> *)
(*               construct_aux cond (x, phi_k) (cd, lit) *)
(*             | ECtx.Drop -> *)
(*               let cond = And [cond; cd] in *)
(*               aux cond  *)
(*           ) *)
(*         let drop_cond = match drop_res with *)
(*           | Some (cond, _) -> cond *)
(*           | None -> None in *)
(*         let ret_regex = match drop_res with *)
(*           | Some (cond, _) -> cond *)
(*           | None -> EpsilonA *)
(*         in *)
(*         | ECtx.RetResLit lit -> *)
(*             let phi = mk_prop_var_eq_lit x lit in *)
(*             (cond, phi_k phi)) *)
(*     | LorA (t1, t2) -> *)
(*         let cond1, r1 = aux cond t1 in *)
(*         let cond2, r2 = aux cond t2 in *)
(*         (Or [ cond1; cond2 ], LorA (r1, r2)) *)
(*     | LandA (t1, t2) -> *)
(*         let cond1, r1 = aux cond t1 in *)
(*         let cond2, r2 = aux cond t2 in *)
(*         (And [ cond1; cond2 ], LandA (r1, r2)) *)
(*     | StarA t -> aux cond (LorA (LorA (EpsilonA, t), SeqA (t, t))) *)
(*     | SigmaA _ -> _failatwith __FILE__ __LINE__ "die" *)
(*   in *)
(*   let _, res = aux mk_true regex in *)
(*   res *)

let purify_bound = 1

let mk_phi_k (localx, r) phi =
  let () =
    Pp.printf "@{<yellow>localx: %s @} <| %s\n" localx.P.x (layout_prop phi)
  in
  let xA = EventA (RetEvent (mk_top_pty localx.Nt.ty)) in
  match get_cbool phi with
  | Some true -> SigmaA { localx; xA; body = r }
  | Some false -> EpsilonA
  | None -> SigmaA { localx; xA; body = SeqA (EventA (GuardEvent phi), r) }

let ret_reduction pctx (k : regex -> regex) se localx : regex -> regex =
 fun r ->
  let pre_regex = k EpsilonA in
  let () = Pp.printf "@{<bold>pre_regex:@} %s\n" (layout_regex pre_regex) in
  let () = Pp.printf "@{<bold>se:@} %s\n" (layout_sevent se) in
  let reversed_regex = delimited_reverse pre_regex in
  let regex =
    reduction_on_op pctx se reversed_regex (localx, mk_phi_k (localx, r))
  in
  let regex = delimited_reverse regex in
  let () = Pp.printf "@{<bold>Result: pre_regex:@} %s\n" (layout_regex regex) in
  regex

let purify_aux pctx (regex : regex) : regex =
  let rec aux k regex =
    let () = Pp.printf "@{<orange>purify_aux: %s @}\n" (layout_regex regex) in
    match regex with
    | EpsilonA -> k EpsilonA
    | EventA _ -> k regex
    | SeqA (t1, t2) -> aux (fun p1 -> aux (fun p2 -> k (SeqA (p1, p2))) t2) t1
    | LorA (t1, t2) -> LorA (aux k t1, aux k t2)
    | LandA (t1, t2) -> LandA (aux k t1, aux k t2)
    | SigmaA { xA = EventA (GuardEvent _); _ } ->
        _failatwith __FILE__ __LINE__ "die"
    | SigmaA { localx; xA; body } -> (
        let phix =
          match xA with
          | EventA se -> (
              match se with
              | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
              | EffEvent _ -> Some (ret_reduction pctx k se localx)
              | RetEvent pty -> (
                  match pty with
                  | ArrPty _ -> None
                  | TuplePty _ -> _failatwith __FILE__ __LINE__ "die"
                  | BasePty { ou = Over; _ } ->
                      _failatwith __FILE__ __LINE__ "die"
                  | BasePty { ou = Under; cty } ->
                      let _, phix = cty_typed_to_prop localx.Nt.x #::: cty in
                      Some (fun r -> k (mk_phi_k (localx, r) phix))))
          | _ -> _failatwith __FILE__ __LINE__ "die"
        in
        match phix with None -> aux k body | Some k -> aux k body)
    | StarA regex -> k (StarA (aux (fun x -> x) regex))
  in
  aux (fun x -> x) regex

let counter = ref 0

let purify (eqctx : ECtx.ctx) (gamma : RCtx.ctx) check
    ({ x = regex; ty = nty } : regex Nt.typed) =
  let () = Pp.printf "@{<bold>purify raw:@} %s\n" (layout_regex regex) in
  let regex = Finalize.finalize regex in
  let () =
    Pp.printf "@{<bold>purify after finalize:@} %s\n" (layout_regex regex)
  in
  let regex = Retilize.retilize nty regex in
  let () =
    Pp.printf "@{<bold>purify after retilize:@} %s\n" (layout_regex regex)
  in
  let actx, regex = Alpha.alpha regex in
  let () =
    Pp.printf "@{<bold>purify after renaming:@} %s\n" (layout_regex regex)
  in
  let (regex : regex) = purify_aux { eqctx; gamma; actx; check } regex in
  let () =
    Pp.printf "@{<bold>purify after purify:@} %s\n" (layout_regex regex)
  in
  let topl, regex = Alpha.to_top_typed_regex regex in
  let () =
    Pp.printf "@{<bold>purify after lift top:@} %s\n" (layout_regex regex)
  in
  let (regex : regex) = Simp.simp regex in
  let () = Pp.printf "@{<bold>purify after simp:@} %s\n" (layout_regex regex) in
  (* let () = if !counter == 1 then failwith "end" else counter := !counter + 1 in *)
  (Alpha.to_rctx topl, regex)

(* (\* NOTE: pretr has no sigma *\) *)
(* let purify_se (eqctx : ECtx.ctx) (gamma : RCtx.ctx) (pre_regex: regex) se = *)
(*   let rec aux regex prop se = *)
(*     match regex with *)
(*     | EpsilonA ->  *)
(*     | SeqA (t1, t2) -> *)
(*       aux (fun se -> (SeqA (t1, k se))) t2 *)
(*     | SigmaA { localx; xA; body } -> *)
(*       aux (fun se -> (SigmaA { localx; xA; body = k se })) body *)
(*     | StarA _ -> _failatwith __FILE__ __LINE__ "star cannot be the last event" *)
(*     | LorA (t1, t2) -> LorA (aux k t1, aux k t2) *)
(*     | EpsilonA -> _failatwith __FILE__ __LINE__ "epsilon cannot be the last event" *)
(*     | LandA (t1, t2) -> LandA (aux k t1, aux k t2) *)
(*     | EventA se -> k se  *)
(*   in *)
(*   aux k regex *)

(* (\* NOTE: box is a special regex variable which is not in the syntax *\) *)
(* let box = EventA (EffEvent { op = "☐"; vs = []; phi = mk_true }) *)

(* let regex_to_boxcont regex = *)
(*   let rec aux regex = *)
(*     match regex with *)
(*     | SeqA (t1, t2) -> SeqA (t1, aux t2) *)
(*     | SigmaA { localx; xA; body } -> *)
(*       SigmaA { localx; xA; body = aux body } *)
(*     | StarA _ -> SeqA (regex, box) *)
(*     | LorA (t1, t2) -> LorA (aux t1, aux t2) *)
(*     | EpsilonA -> _failatwith __FILE__ __LINE__ "die" *)
(*     | LandA (_, _) -> _failatwith __FILE__ __LINE__ "conjunction will not happen before purify" *)
(*     | EventA (GuardEvent _) -> SeqA (regex, box) *)
(*     | EventA (RetEvent pty) -> *)
(*       (match pty with *)
(*        | TuplePty _ -> _failatwith __FILE__ __LINE__ "die" *)
(*        | BasePty {ou = Over; _} -> _failatwith __FILE__ __LINE__ "die" *)
(*        | ArrPty _ -> box *)
(*        | BasePty {ou = Under; cty} ->  *)
(*       ) *)
(*     | EventA se -> EventA  *)
(*   in *)
(*   aux regex *)

(* let purify_typectx (eqctx : ECtx.ctx) (k : regex_cont) (typectx : RCtx.ctx) : *)
(*     RCtx.ctx * regex_cont = *)
(*   let fold_aux (pure_typectx, k) x = *)
(*     match x.ty with *)
(*     | Pty _ -> (pure_typectx @ [ x ], k) *)
(*     | Regty Nt.{ x = regex; ty = nty } -> *)
(*         let x = Nt.( #: ) x.x nty in *)

(*   in *)
(*   RCtx.fold_left fold_aux (RCtx.empty, k) typectx *)
