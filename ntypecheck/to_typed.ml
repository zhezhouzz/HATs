open Sugar
module T = Ast.TypedTermlang
open Ast.OptTypedTermlang

let rec to_opttyped (type a b) (f : a -> b) (expr : a T.typed) : b typed =
  (f expr.T.x) #: (Some expr.T.ty)

and to_opttyped_id : 'a T.typed -> 'a typed =
 fun expr -> expr.T.x #: (Some expr.T.ty)

and to_opttyped_hd : T.handler T.typed -> handler typed =
 fun expr -> (handler_to_opthandler expr.T.x) #: (Some expr.T.ty)

and to_opttyped_term : T.term T.typed -> term typed =
 fun expr -> (term_to_optterm expr.T.x) #: (Some expr.T.ty)

and term_to_optterm (expr : T.term) : term =
  match expr with
  | T.Err -> Err
  | T.Tu es -> Tu (List.map to_opttyped_term es)
  | T.Var var -> Var var
  | T.Const v -> Const v
  | T.Lam { lamarg; lambody } ->
      Lam { lamarg = to_opttyped_id lamarg; lambody = to_opttyped_term lambody }
  | T.VHd hd -> VHd (to_opttyped_hd hd)
  | T.(Let { if_rec; lhs; rhs; letbody }) ->
      Let
        {
          if_rec;
          lhs = List.map to_opttyped_id lhs;
          rhs = to_opttyped_term rhs;
          letbody = to_opttyped_term letbody;
        }
  | T.(AppOp (op, args)) ->
      AppOp (to_opttyped (fun x -> x) op, List.map to_opttyped_term args)
  | T.(Perform { rhsop; rhsargs }) ->
      Perform
        {
          rhsop = to_opttyped_id rhsop;
          rhsargs = List.map to_opttyped_term rhsargs;
        }
  | T.(CWithH { handler; handled_prog }) ->
      CWithH
        {
          handler = to_opttyped_hd handler;
          handled_prog = to_opttyped_term handled_prog;
        }
  | T.(App (func, args)) ->
      App (to_opttyped_term func, List.map to_opttyped_term args)
  | T.(Ite (e1, e2, e3)) ->
      Ite (to_opttyped_term e1, to_opttyped_term e2, to_opttyped_term e3)
  | T.(Match (case_target, cs)) ->
      Match
        (to_opttyped_term case_target, List.map match_case_to_optmatch_case cs)

and match_case_to_optmatch_case T.{ constructor; args; exp } =
  {
    constructor = to_opttyped (fun x -> x) constructor;
    args = List.map to_opttyped_id args;
    exp = to_opttyped_term exp;
  }

and handler_case_to_opthandler_case T.{ effop; effargs; effk; hbody } =
  {
    effop = to_opttyped_id effop;
    effargs = List.map to_opttyped_id effargs;
    effk = to_opttyped_id effk;
    hbody = to_opttyped_term hbody;
  }

and ret_case_to_optret_case T.{ retarg; retbody } =
  { retarg = to_opttyped_id retarg; retbody = to_opttyped_term retbody }

and handler_to_opthandler T.{ ret_case; handler_cases } : handler =
  {
    ret_case = ret_case_to_optret_case ret_case;
    handler_cases = List.map handler_case_to_opthandler_case handler_cases;
  }

module L = Ast.OptTypedTermlang
open Ast.TypedTermlang

let rec to_typed (type a b) (f : a -> b) (expr : a L.typed) : b typed =
  match expr.L.ty with
  | None -> _failatwith __FILE__ __LINE__ "untyped"
  | Some ty -> (f expr.L.x) #: ty

and to_typed_id : 'a L.typed -> 'a typed =
 fun expr ->
  match expr.L.ty with
  | None -> _failatwith __FILE__ __LINE__ "untyped"
  | Some ty -> expr.L.x #: ty

and to_typed_hd : L.handler L.typed -> handler typed =
 fun expr ->
  match expr.L.ty with
  | None -> _failatwith __FILE__ __LINE__ "untyped"
  | Some ty -> (handler_to_handler expr.L.x) #: ty

and to_typed_term : L.term L.typed -> term typed =
 fun expr ->
  match expr.L.ty with
  | None -> _failatwith __FILE__ __LINE__ "untyped"
  | Some ty -> (term_to_term expr.L.x) #: ty

and term_to_term (expr : L.term) : term =
  match expr with
  | L.Err -> Err
  | L.Tu es -> Tu (List.map to_typed_term es)
  | L.Var var -> Var var
  | L.Const v -> Const v
  | L.Lam { lamarg; lambody } ->
      Lam { lamarg = to_typed_id lamarg; lambody = to_typed_term lambody }
  | L.VHd hd -> VHd (to_typed_hd hd)
  | L.(Let { if_rec; lhs; rhs; letbody }) ->
      Let
        {
          if_rec;
          lhs = List.map to_typed_id lhs;
          rhs = to_typed_term rhs;
          letbody = to_typed_term letbody;
        }
  | L.(AppOp (op, args)) ->
      AppOp (to_typed (fun x -> x) op, List.map to_typed_term args)
  | L.(Perform { rhsop; rhsargs }) ->
      Perform
        { rhsop = to_typed_id rhsop; rhsargs = List.map to_typed_term rhsargs }
  | L.(CWithH { handler; handled_prog }) ->
      CWithH
        {
          handler = to_typed_hd handler;
          handled_prog = to_typed_term handled_prog;
        }
  | L.(App (func, args)) -> App (to_typed_term func, List.map to_typed_term args)
  | L.(Ite (e1, e2, e3)) ->
      Ite (to_typed_term e1, to_typed_term e2, to_typed_term e3)
  | L.(Match (case_target, cs)) ->
      Match (to_typed_term case_target, List.map match_case_to_match_case cs)

and match_case_to_match_case L.{ constructor; args; exp } =
  {
    constructor = to_typed (fun x -> x) constructor;
    args = List.map to_typed_id args;
    exp = to_typed_term exp;
  }

and handler_case_to_handler_case L.{ effop; effargs; effk; hbody } =
  {
    effop = to_typed_id effop;
    effargs = List.map to_typed_id effargs;
    effk = to_typed_id effk;
    hbody = to_typed_term hbody;
  }

and ret_case_to_ret_case L.{ retarg; retbody } =
  { retarg = to_typed_id retarg; retbody = to_typed_term retbody }

and handler_to_handler L.{ ret_case; handler_cases } : handler =
  {
    ret_case = ret_case_to_ret_case ret_case;
    handler_cases = List.map handler_case_to_handler_case handler_cases;
  }

open Ast.Structure
module S = Ast.StructureRaw

let to_typed_struct f =
  List.map (fun code ->
      match code with
      | S.Mps mps -> Mps mps
      | S.Type_dec d -> Type_dec d
      | S.Func_dec d -> Func_dec d
      | S.FuncImp { name; if_rec; body } ->
          FuncImp { name; if_rec; body = f name if_rec body }
      | S.Rty _ -> _failatwith __FILE__ __LINE__ "unimp")

open Ast.StructureRaw
module U = Ast.Structure

let to_opttyped_struct =
  List.map (fun code ->
      match code with
      | U.Mps mps -> Mps mps
      | U.Type_dec d -> Type_dec d
      | U.Func_dec d -> Func_dec d
      | U.FuncImp { name; if_rec; body } ->
          FuncImp { name; if_rec; body = term_to_optterm body }
      | U.Rty _ -> _failatwith __FILE__ __LINE__ "unimp")
