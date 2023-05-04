module F (L : Lit.T) = struct
  include L

  type prop =
    | Lit of lit
    | Implies of prop * prop
    | Ite of prop * prop * prop
    | Not of prop
    | And of prop list
    | Or of prop list
    | Iff of prop * prop
    | Forall of string Normalty.Ntyped.typed * prop
    | Exists of string Normalty.Ntyped.typed * prop

  let get_cbool = function Lit (AC (Constant.B b)) -> Some b | _ -> None
  let mk_true = Lit mk_lit_true
  let mk_false = Lit mk_lit_false
  let is_true p = match get_cbool p with Some true -> true | _ -> false
  let is_false p = match get_cbool p with Some false -> true | _ -> false
  let smart_and l = And (List.filter (fun p -> not (is_true p)) l)
  let smart_or l = Or (List.filter (fun p -> not (is_false p)) l)
  let smart_implies (a, b) = if is_true a then b else Implies (a, b)

  let subst_prop (y, f) e =
    let rec aux e =
      match e with
      | Lit lit -> Lit (subst_lit (y, f) lit)
      | Implies (e1, e2) -> Implies (aux e1, aux e2)
      | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
      | Not e -> Not (aux e)
      | And es -> And (List.map aux es)
      | Or es -> Or (List.map aux es)
      | Iff (e1, e2) -> Iff (aux e1, aux e2)
      | Forall (u, body) ->
          if String.equal u.x y then e else Forall (u, aux body)
      | Exists (u, body) ->
          if String.equal u.x y then e else Exists (u, aux body)
    in
    aux e

  let prop_multisubst = List.fold_right subst_prop
  let subst_prop_id (y, z) e = subst_prop (y.x, AVar z) e
end
