module F (L : Lit.T) = struct
  open L

  type eqterm =
    | EqtRet of string
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
    | EqtDo { dolhs = d1; effop = op1; effargs = args1; body = EqtRet d2 }
      when op == op1 && d2 == d1 ->
        Some args1
    | _ -> None

  let get_2_by_last_op op1' op2' = function
    | EqtDo
        {
          dolhs = d1;
          effop = op1;
          effargs = args1;
          body =
            EqtDo { dolhs = d2; effop = op2; effargs = args2; body = EqtRet d3 };
        }
      when op1' == op1 && op2' == op2 && d2 == d3 ->
        Some ((d1, args1), args2)
    | _ -> None

  open Zzdatatype.Datatype
  open Sugar

  type ret_res = RetResLit of lit | Drop

  let instantiate_lit m lit =
    let fv = fv_lit lit in
    List.fold_left
      (fun lit x ->
        let x' = StrMap.find "instantiate_lit" m x in
        subst_lit (x, x') lit)
      lit fv

  let instantiate_cond m cond = List.map (fun lit -> instantiate_lit m lit) cond

  let match_obv_equation_one_aux (e, cond) retname (op1, args1, op2, args2) =
    match get_1_by_last_op op2 e with
    | Some args2' ->
        let m =
          StrMap.from_kv_list @@ _safe_combine __FILE__ __LINE__ args2' args2
        in
        let lit = StrMap.find "match_obv_equation" m retname in
        let cond = instantiate_cond m cond in
        Some (RetResLit lit, cond)
    | None -> (
        match get_2_by_last_op op1 op2 e with
        | Some ((d1, args1'), args2') ->
            let m =
              StrMap.from_kv_list
              @@ _safe_combine __FILE__ __LINE__ (args1' @ args2')
                   (args1 @ args2)
            in
            let cond = instantiate_cond m cond in
            if String.equal d1 retname then Some (Drop, cond)
            else
              let lit = StrMap.find "match_obv_equation" m retname in
              Some (RetResLit lit, cond)
        | None -> None)

  let match_obv_equation_one e key =
    match e with
    | EqObv { elhs; erhs = EqtRet retname; cond } ->
        match_obv_equation_one_aux (elhs, cond) retname key
    | _ -> None

  let match_obv_equation eqs key =
    let res = List.filter_map (fun e -> match_obv_equation_one e key) eqs in
    match res with
    | [] ->
        _failatwith __FILE__ __LINE__
          "the operational semantics of the effects are not compelete"
    | _ -> res
end
