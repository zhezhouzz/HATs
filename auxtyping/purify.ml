open Language
module RCtx = RTypectx
module P = Rty.P
module ECtx = Eqctx
open Rty
open Sugar

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

let reduction_single_on_op pctx pre se1 se2 =
  let op1, vs1, phi1 = se_force_op se1 in
  let op2, vs2, phi2 = se_force_op se2 in
  let args1 = List.map (fun x -> find_lit_assignment_from_prop phi1 x) vs1 in
  let args2 = List.map (fun x -> find_lit_assignment_from_prop phi2 x) vs2 in
  let res = ECtx.find_ret_rules pctx.eqctx (op1, args1) (op2, args2) in
  let cond_to_cond_prop eqconds =
    P.(And (List.map (fun lit -> Lit lit) eqconds))
  in
  let res =
    List.filter_map
      (fun (res, cond) ->
        let cond = cond_to_cond_prop cond in
        if check_prop_valid pctx (And [ pre; cond ]) then Some (cond, res)
        else None)
      res
  in
  match res with [ res ] -> res | _ -> _failatwith __FILE__ __LINE__ "die"
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

let reduction_on_op pctx se regex (x, phi_k) =
  let rec aux cond regex =
    match regex with
    | EpsilonA -> (mk_true, phi_k cond)
    | SeqA (t1, t2) ->
        let cond1, res1 = aux cond t1 in
        let res1 = SeqA (res1, t2) in
        let cond2, res2 = aux (And [ cond1; cond ]) t2 in
        (cond2, LorA (res1, res2))
    | EventA se1 -> (
        let cond, res = reduction_single_on_op pctx cond se1 se in
        match res with
        | ECtx.Drop -> (cond, EpsilonA)
        | ECtx.RetResLit lit ->
            let phi = mk_prop_var_eq_lit x lit in
            (cond, phi_k phi))
    | LorA (t1, t2) ->
        let cond1, r1 = aux cond t1 in
        let cond2, r2 = aux cond t2 in
        (Or [ cond1; cond2 ], LorA (r1, r2))
    | LandA (t1, t2) ->
        let cond1, r1 = aux cond t1 in
        let cond2, r2 = aux cond t2 in
        (And [ cond1; cond2 ], LandA (r1, r2))
    | StarA t -> aux cond (LorA (LorA (EpsilonA, t), SeqA (t, t)))
    | SigmaA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let _, res = aux mk_true regex in
  res

let purify_bound = 1

let mk_phi_k (localx, r) phi =
  let xA = EventA (RetEvent (mk_top_pty localx.Nt.ty)) in
  SigmaA { localx; xA; body = SeqA (EventA (GuardEvent phi), r) }

let ret_reduction pctx (k : regex -> regex) se localx : regex -> regex =
 fun r ->
  let pre_regex = k EpsilonA in
  let reversed_regex = delimited_reverse pre_regex in
  let regex =
    reduction_on_op pctx se reversed_regex (localx, mk_phi_k (localx, r))
  in
  delimited_reverse regex

let purify_aux pctx (regex : regex) : regex =
  let rec aux k regex =
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
                      Some (fun r -> mk_phi_k (localx, r) phix)))
          | _ -> _failatwith __FILE__ __LINE__ "die"
        in
        match phix with None -> aux k body | Some k -> aux k body)
    | StarA regex -> k (StarA (aux (fun x -> x) regex))
  in
  aux (fun x -> x) regex

let purify (eqctx : ECtx.ctx) (gamma : RCtx.ctx) check
    ({ x = regex; ty = nty } : regex Nt.typed) =
  let regex = Finalize.finalize regex in
  let regex = Retilize.retilize nty regex in
  let actx, regex = Alpha.alpha regex in
  let (regex : regex) = purify_aux { eqctx; gamma; actx; check } regex in
  let topl, regex = Alpha.to_top_typed_regex regex in
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
