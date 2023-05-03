module F (L : Lit.T) = struct
  include Pred.F (L)

  type t =
    | Pred of pred
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | Forall of string Normalty.Ntyped.typed * t
    | Exists of string Normalty.Ntyped.typed * t

  let get_cbool = function
    | Pred (Lit (AC (Constant.B b))) -> Some b
    | _ -> None

  let mk_true = Pred mk_pred_true
  let mk_false = Pred mk_pred_false
  let is_true p = match get_cbool p with Some true -> true | _ -> false
  let is_false p = match get_cbool p with Some false -> true | _ -> false
  let smart_and l = And (List.filter (fun p -> not (is_true p)) l)
  let smart_or l = Or (List.filter (fun p -> not (is_false p)) l)
  let smart_implies (a, b) = if is_true a then b else Implies (a, b)

  let subst (y, f) e =
    let rec aux e =
      match e with
      | Pred pred -> Pred (pred_subst (y, f) pred)
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

  let multisubst = List.fold_right subst
  let subst_id (y, z) e = subst (y.x, AVar z) e
end
