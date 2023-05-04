open Syntax
module Raw = StructureRaw
open Structure
open Coersion_aux

let rec force_typed_term lit = force __FILE__ __LINE__ R.(force_term #-> lit)

and force_term term =
  match term with
  | Raw.Err -> Err
  | Raw.Tu es -> Tu (List.map force_typed_term es)
  | Raw.Var var -> Var var
  | Raw.Const v -> Const v
  | Raw.Lam { lamarg; lambody } ->
      Lam
        {
          lamarg = force __FILE__ __LINE__ lamarg;
          lambody = force_typed_term lambody;
        }
  | Raw.(Let { if_rec; lhs; rhs; letbody }) ->
      Let
        {
          if_rec;
          lhs = List.map (force __FILE__ __LINE__) lhs;
          rhs = force_typed_term rhs;
          letbody = force_typed_term letbody;
        }
  | Raw.(AppOp (op, args)) ->
      AppOp (force __FILE__ __LINE__ op, List.map force_typed_term args)
  | Raw.(App (func, args)) ->
      App (force_typed_term func, List.map force_typed_term args)
  | Raw.(Ite (e1, e2, e3)) ->
      Ite (force_typed_term e1, force_typed_term e2, force_typed_term e3)
  | Raw.(Match (case_target, cs)) ->
      Match (force_typed_term case_target, List.map force_match_case cs)

and force_match_case Raw.{ constructor; args; exp } =
  {
    constructor = force __FILE__ __LINE__ constructor;
    args = List.map (force __FILE__ __LINE__) args;
    exp = force_typed_term exp;
  }

let rec besome_typed_term lit = besome besome_term #-> lit

and besome_term term =
  match term with
  | Err -> Raw.Err
  | Tu es -> Raw.Tu (List.map besome_typed_term es)
  | Var var -> Raw.Var var
  | Const v -> Raw.Const v
  | Lam { lamarg; lambody } ->
      Raw.Lam { lamarg = besome lamarg; lambody = besome_typed_term lambody }
  | Let { if_rec; lhs; rhs; letbody } ->
      Raw.Let
        {
          if_rec;
          lhs = List.map besome lhs;
          rhs = besome_typed_term rhs;
          letbody = besome_typed_term letbody;
        }
  | AppOp (op, args) -> Raw.AppOp (besome op, List.map besome_typed_term args)
  | App (func, args) ->
      Raw.App (besome_typed_term func, List.map besome_typed_term args)
  | Ite (e1, e2, e3) ->
      Raw.Ite (besome_typed_term e1, besome_typed_term e2, besome_typed_term e3)
  | Match (case_target, cs) ->
      Raw.Match (besome_typed_term case_target, List.map besome_match_case cs)

and besome_match_case { constructor; args; exp } =
  Raw.
    {
      constructor = besome constructor;
      args = List.map besome args;
      exp = besome_typed_term exp;
    }
