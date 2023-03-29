module F (Ty : Typed.T) = struct
  include Ty

  type lit =
    | AC of Constant.t
    | AVar of string typed
    | APair of lit * lit
    | AFst of lit
    | ASnd of lit
    | AApp of string typed * lit list

  type t =
    | Lit of lit
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | MethodPred of string typed * lit list
    | Forall of string Normalty.Ntyped.typed * t
    | Exists of string Normalty.Ntyped.typed * t

  let f_pair = "pair"
  let f_fst = "fst"
  let f_snd = "snd"
  let f_select = "select"
  let f_len = "len"
  let mk_true = Lit (AC (Constant.B true))
  let mk_false = Lit (AC (Constant.B false))

  let subst_lit_ (y, f) e =
    let rec aux e =
      match e with
      | AC _ -> e
      | AVar x -> if String.equal x.x y then f x else e
      | APair (a, b) -> APair (aux a, aux b)
      | AFst a -> AFst (aux a)
      | ASnd a -> ASnd (aux a)
      | AApp (f, args) -> AApp (f, List.map aux args)
    in
    aux e

  let subst_id_lit (y, z) e = subst_lit_ (y, fun x -> AVar z #: x.ty) e
  let subst_lit (y, lit) e = subst_lit_ (y, fun _ -> lit) e
  let multisubst_lit l e = List.fold_right subst_lit l e

  let subst_id (y, z) e =
    let rec aux e =
      match e with
      | Lit lit -> Lit (subst_id_lit (y, z) lit)
      | Implies (e1, e2) -> Implies (aux e1, aux e2)
      | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
      | Not e -> Not (aux e)
      | And es -> And (List.map aux es)
      | Or es -> Or (List.map aux es)
      | Iff (e1, e2) -> Iff (aux e1, aux e2)
      | MethodPred (mp, args) ->
          MethodPred (mp, List.map (subst_id_lit (y, z)) args)
      | Forall (u, body) ->
          if String.equal u.x y then e else Forall (u, aux body)
      | Exists (u, body) ->
          if String.equal u.x y then e else Exists (u, aux body)
    in
    aux e
end
