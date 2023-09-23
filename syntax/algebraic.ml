module F (L : Lit.T) = struct
  open L
  open Zzdatatype.Datatype
  open Sugar

  type eqterm =
    | EqtRet of lit
    | EqtDo of {
        dolhs : string;
        effop : string;
        effargs : string list;
        body : eqterm;
      }

  type equation =
    | EqObv of { elhs : eqterm; erhs : eqterm; cond : lit list }
    | EqState of { elhs : eqterm; erhs : eqterm }

  let get_1_by_last_op op = function
    | EqtDo
        { dolhs = d1; effop = op1; effargs = args1; body = EqtRet (AVar d2) }
      when String.equal op op1 && String.equal d2 d1 ->
        Some args1
    | _ -> None

  let get_2_by_last_op op1' op2' = function
    | EqtDo
        {
          dolhs = d1;
          effop = op1;
          effargs = args1;
          body =
            EqtDo
              {
                dolhs = d2;
                effop = op2;
                effargs = args2;
                body = EqtRet (AVar d3);
              };
        }
      when String.equal op1' op1 && String.equal op2' op2 && String.equal d2 d3
      ->
        Some ((d1, args1), args2)
    | _ -> None

  type ret_res = RetResLit of lit | Drop

  let instantiate_lit m lit =
    let fv = fv_lit lit in
    List.fold_left
      (fun lit x ->
        let x' = StrMap.find "instantiate_lit" m x in
        subst_lit (x, x') lit)
      lit fv

  let instantiate_cond m cond = List.map (fun lit -> instantiate_lit m lit) cond

  let match_obv1_equation_one_aux (e, cond) retlit (op2, args2) =
    match get_1_by_last_op op2 e with
    | Some args2' ->
        let m =
          StrMap.from_kv_list @@ _safe_combine __FILE__ __LINE__ args2' args2
        in
        let lit = instantiate_lit m retlit in
        let cond = instantiate_cond m cond in
        Some (RetResLit lit, cond)
    | None -> None

  let match_obv2_equation_one_aux (e, cond) retlit (op1, args1) (op2, args2) =
    match get_2_by_last_op op1 op2 e with
    | Some ((d1, args1'), args2') ->
        let m =
          StrMap.from_kv_list
          @@ _safe_combine __FILE__ __LINE__ (args1' @ args2') (args1 @ args2)
        in
        let cond = instantiate_cond m cond in
        if eq_lit (AVar d1) retlit then Some (Drop, cond)
        else
          let lit = instantiate_lit m retlit in
          Some (RetResLit lit, cond)
    | None -> None

  let match_obv1_equation_one e key =
    match e with
    | EqObv { elhs; erhs = EqtRet retlit; cond } ->
        match_obv1_equation_one_aux (elhs, cond) retlit key
    | _ -> None

  let match_obv2_equation_one e key1 key2 =
    match e with
    | EqObv { elhs; erhs = EqtRet retlit; cond } ->
        match_obv2_equation_one_aux (elhs, cond) retlit key1 key2
    | _ -> None

  let match_equation_1op eqs key =
    let res = List.filter_map (fun e -> match_obv1_equation_one e key) eqs in
    match res with
    | [] ->
        _failatwith __FILE__ __LINE__
          "the operational semantics of the effects are not compelete"
    | _ -> res

  let match_equation_2op eqs key1 key2 =
    let res =
      List.filter_map (fun e -> match_obv2_equation_one e key1 key2) eqs
    in
    let res' = List.filter_map (fun e -> match_obv1_equation_one e key2) eqs in
    match res @ res' with
    | [] ->
        _failatwith __FILE__ __LINE__
          "the operational semantics of the effects are not compelete"
    | _ -> res
end
