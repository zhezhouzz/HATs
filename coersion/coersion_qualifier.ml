open Syntax
module Raw = RtyRaw
open Rty

let force_qualifier qualifier =
  let rec aux qualifier =
    match qualifier with
    | Raw.Lit qualifier -> Lit (Coersion_lit.force_lit qualifier)
    | Raw.Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Raw.Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Raw.Not e -> Not (aux e)
    | Raw.And es -> And (List.map aux es)
    | Raw.Or es -> Or (List.map aux es)
    | Raw.Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Raw.Forall (u, e) -> Forall (u, aux e)
    | Raw.Exists (u, e) -> Exists (u, aux e)
  in
  aux qualifier

let besome_qualifier qualifier =
  let rec aux qualifier =
    match qualifier with
    | Lit lit -> Raw.Lit (Coersion_lit.besome_lit lit)
    | Implies (e1, e2) -> Raw.Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Raw.Ite (aux e1, aux e2, aux e3)
    | Not e -> Raw.Not (aux e)
    | And es -> Raw.And (List.map aux es)
    | Or es -> Raw.Or (List.map aux es)
    | Iff (e1, e2) -> Raw.Iff (aux e1, aux e2)
    | Forall (u, e) -> Raw.Forall (u, aux e)
    | Exists (u, e) -> Raw.Exists (u, aux e)
  in
  aux qualifier
