open Ast.Rty
module R = Ast.RtyRaw
open Sugar

let force_typed R.P.{ x; ty } =
  match ty with
  | None -> _failatwith __FILE__ __LINE__ "force_typed"
  | Some ty -> Nt.(x #: ty)

let to_opt_ Nt.{ x; ty } = R.P.(x #: (Some ty))

open P

let rec force_typed_lit = function
  | R.P.AC c -> AC c
  | R.P.AVar x -> AVar (force_typed x)
  | R.P.ATu l -> ATu (List.map force_typed_lit l)
  | R.P.AProj (n, total, a) -> AProj (n, total, force_typed_lit a)
  | R.P.AApp (f, args) -> AApp (force_typed f, List.map force_typed_lit args)

let rec to_opt_lit = function
  | AC c -> R.P.AC c
  | AVar x -> R.P.AVar (to_opt_ x)
  | ATu l -> R.P.ATu (List.map to_opt_lit l)
  | AProj (n, total, a) -> R.P.AProj (n, total, to_opt_lit a)
  | AApp (f, args) -> R.P.AApp (to_opt_ f, List.map to_opt_lit args)

let force_typed_qualifier =
  let rec aux = function
    | R.P.Lit lit -> Lit (force_typed_lit lit)
    | R.P.Implies (e1, e2) -> Implies (aux e1, aux e2)
    | R.P.Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | R.P.Not e -> Not (aux e)
    | R.P.And es -> And (List.map aux es)
    | R.P.Or es -> Or (List.map aux es)
    | R.P.Iff (e1, e2) -> Iff (aux e1, aux e2)
    | R.P.MethodPred (mp, args) ->
        MethodPred (force_typed mp, List.map force_typed_lit args)
    | R.P.Forall (u, e) -> Forall (u, aux e)
    | R.P.Exists (u, e) -> Exists (u, aux e)
  in
  aux

let to_opt_qualifier =
  let rec aux = function
    | Lit lit -> R.P.Lit (to_opt_lit lit)
    | Implies (e1, e2) -> R.P.Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> R.P.Ite (aux e1, aux e2, aux e3)
    | Not e -> R.P.Not (aux e)
    | And es -> R.P.And (List.map aux es)
    | Or es -> R.P.Or (List.map aux es)
    | Iff (e1, e2) -> R.P.Iff (aux e1, aux e2)
    | MethodPred (mp, args) ->
        R.P.MethodPred (to_opt_ mp, List.map to_opt_lit args)
    | Forall (u, e) -> R.P.Forall (u, aux e)
    | Exists (u, e) -> R.P.Exists (u, aux e)
  in
  aux

let force_typed_ou = function R.Over -> Over | R.Under -> Under
let to_opt_ou = function Over -> R.Over | Under -> R.Under
let force_typed_dep = function R.Sigma -> Sigma | R.Pi -> Pi
let to_opt_dep = function Sigma -> R.Sigma | Pi -> R.Pi
let force_typed_basety R.{ v; phi } = { v; phi = force_typed_qualifier phi }
let to_opt_basety { v; phi } = R.{ v; phi = to_opt_qualifier phi }

let force_typed_rty =
  let rec aux = function
    | R.Traced { h; pre; rty; post } ->
        Traced
          {
            h;
            pre = force_typed_basety pre;
            rty = aux rty;
            post = force_typed_basety post;
          }
    | R.BaseRty { ou; basety } ->
        BaseRty { ou = force_typed_ou ou; basety = force_typed_basety basety }
    | R.DepRty { dep; label; rarg; retrty } ->
        let R.{ x; ty } = rarg in
        let rarg = Ast.Rty.{ x; ty = aux ty } in
        DepRty { dep = force_typed_dep dep; label; rarg; retrty = aux retrty }
  in
  aux

let to_opt_rty =
  let rec aux = function
    | Traced { h; pre; rty; post } ->
        R.Traced
          {
            h;
            pre = to_opt_basety pre;
            rty = aux rty;
            post = to_opt_basety post;
          }
    | BaseRty { ou; basety } ->
        R.BaseRty { ou = to_opt_ou ou; basety = to_opt_basety basety }
    | DepRty { dep; label; rarg; retrty } ->
        let Ast.Rty.{ x; ty } = rarg in
        let rarg = R.{ x; ty = aux ty } in
        R.DepRty { dep = to_opt_dep dep; label; rarg; retrty = aux retrty }
  in
  aux
