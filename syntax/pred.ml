module F (L : Lit.T) = struct
  include L

  type pred = Lit of lit | MethodPred of string typed * lit typed list

  let mk_pred_true = Lit mk_lit_true
  let mk_pred_false = Lit mk_lit_false

  let pred_subst (y, lit) e =
    let aux e =
      match e with
      | Lit lit -> Lit (lit_subst (y, lit) lit)
      | MethodPred (mp, ls) ->
          MethodPred (mp, List.map (fun x -> (lit_subst (y, lit)) #-> x) ls)
    in
    aux e
end
