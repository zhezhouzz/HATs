open Z3
open Z3aux
open Language.Rty.P
open Sugar

let to_z3 ctx prop =
  let rec aux prop =
    match prop with
    | Implies (p1, p2) -> Z3.Boolean.mk_implies ctx (aux p1) (aux p2)
    | Ite (p1, p2, p3) -> Z3.Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
    | Not p -> Z3.Boolean.mk_not ctx (aux p)
    | And ps -> Z3.Boolean.mk_and ctx (List.map aux ps)
    | Or ps -> Z3.Boolean.mk_or ctx (List.map aux ps)
    | Iff (p1, p2) -> Z3.Boolean.mk_iff ctx (aux p1) (aux p2)
    | Forall (u, body) ->
        make_forall ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] (aux body)
    | Exists (u, body) ->
        make_exists ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] (aux body)
    | Lit lit -> Litencoding.typed_lit_to_z3 ctx lit #: Nt.bool_ty
  in
  aux prop

(* tail recursoin version *)

type tmp =
  | TImplies0
  | TImplies1 of Expr.expr
  | TIte0
  | TIte1 of Expr.expr
  | TIte2 of Expr.expr * Expr.expr
  | TNot
  | TIff0
  | TIff1 of Expr.expr
  | TForall of Expr.expr
  | TExists of Expr.expr
  | TStop of Expr.expr

let machine ctx expr = function
  | TImplies0 -> TImplies1 expr
  | TIte0 -> TIte1 expr
  | TIte1 e1 -> TIte2 (e1, expr)
  | TIff0 -> TIff1 expr
  | TImplies1 e1 -> TStop (Z3.Boolean.mk_implies ctx e1 expr)
  | TIte2 (e1, e2) -> TStop (Z3.Boolean.mk_ite ctx e1 e2 expr)
  | TNot -> TStop (Z3.Boolean.mk_not ctx expr)
  | TIff1 e1 -> TStop (Z3.Boolean.mk_iff ctx e1 expr)
  | TForall u -> TStop (make_forall ctx [ u ] expr)
  | TExists u -> TStop (make_exists ctx [ u ] expr)
  | TStop _ -> _failatwith __FILE__ __LINE__ ""

let to_z3_tail ctx prop =
  let rec aux c prop =
    match prop with
    | Implies (p1, p2) ->
        aux
          (fun p2 -> aux (fun p1 -> c (Z3.Boolean.mk_implies ctx p1 p2)) p1)
          p2
    | Ite (p1, p2, p3) ->
        aux
          (fun p3 ->
            aux
              (fun p2 -> aux (fun p1 -> c (Z3.Boolean.mk_ite ctx p1 p2 p3)) p1)
              p2)
          p3
    | Not p -> aux (fun p -> c (Z3.Boolean.mk_not ctx p)) p
    | And ps -> aux_multi (fun ps -> c (Z3.Boolean.mk_and ctx ps)) ps
    | Or ps -> aux_multi (fun ps -> c (Z3.Boolean.mk_or ctx ps)) ps
    | Iff (p1, p2) ->
        aux (fun p2 -> aux (fun p1 -> c (Z3.Boolean.mk_iff ctx p1 p2)) p1) p2
    | Forall (u, body) ->
        aux
          (fun body ->
            c (make_forall ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] body))
          body
    | Exists (u, body) ->
        aux
          (fun body ->
            c (make_exists ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] body))
          body
    | Lit lit -> c (Litencoding.typed_lit_to_z3 ctx lit #: Nt.bool_ty)
  and aux_multi cs props =
    match props with
    | [] -> cs []
    | h :: t -> aux (fun h -> aux_multi (fun t -> cs (h :: t)) t) h
  in
  aux (fun p -> p) prop
