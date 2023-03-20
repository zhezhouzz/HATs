open Language
module Typectx = NTypectx
open Zzdatatype.Datatype
open Sugar
open OptTypedTermlang
module NTyped = Normalty.Ntyped
open Aux
(* module L = TypedTermlang *)

let _unify = _type_unify
let _unify_ = NTyped._type_unify_

let _unify_update file line ty' { x; ty } =
  x #: (_unify file line (Some ty') ty)

let _solve_by_argsty file line fty argsty' =
  let open NTyped in
  let argsty, retty = destruct_arr_tp fty in
  let m, argsty_ =
    _unify_ file line StrMap.empty (mk_tuple argsty) (mk_tuple argsty')
  in
  let argsty =
    match argsty_ with
    | Ty_tuple argsty -> argsty
    | _ -> _failatwith __FILE__ __LINE__ "?"
  in
  let retty = subst_m m retty in
  (argsty, retty)

let _solve_by_retty file line fty retty' =
  let open NTyped in
  let argsty, retty = destruct_arr_tp fty in
  let m, retty = _unify_ file line StrMap.empty retty retty' in
  let subst m t =
    let rec aux t =
      match t with
      | Ty_var n -> (
          match StrMap.find_opt m n with None -> t | Some ty -> ty)
      | Ty_list t -> Ty_list (aux t)
      | Ty_arrow (l, t1, t2) -> Ty_arrow (l, aux t1, aux t2)
      | Ty_tuple ts -> Ty_tuple (List.map aux ts)
      | Ty_constructor (id, ts) -> Ty_constructor (id, List.map aux ts)
      | _ -> t
    in
    aux t
  in
  let argsty = List.map (subst m) argsty in
  (argsty, retty)

let force_typed { x; ty } =
  match ty with
  | None -> _failatwith __FILE__ __LINE__ "?"
  | Some ty -> NTyped.{ x; ty }

let type_check (topctx : Typectx.ctx) (x : term typed) (tyopt : t) : term typed
    =
  let rec bidirect_infer (ctx : Typectx.ctx) (x : term typed) :
      term typed * NTyped.t =
    match x.ty with None -> infer ctx x.x | Some ty -> (check ctx x.x ty, ty)
  and bidirect_check (ctx : Typectx.ctx) (x : term typed) (ty : NTyped.t) :
      term typed =
    match x.ty with
    | None -> check ctx x.x ty
    | Some ty' ->
        let ty = NTyped._type_unify __FILE__ __LINE__ ty' ty in
        check ctx x.x ty
  and check (ctx : Typectx.ctx) (x : term) (ty : NTyped.t) : term typed =
    match (x, ty) with
    | Err, _ -> Err #: (Some ty)
    | Const _, _
    | Var _, _
    | AppOp (_, _), _
    | VHd _, _
    | Perform _, _
    | CWithH _, _ ->
        let x, ty' = infer ctx x in
        _unify_update __FILE__ __LINE__ ty' x
    | Tu es, Ty_tuple tys ->
        let estys = _safe_combine __FILE__ __LINE__ es tys in
        let es = List.map (fun (e, ty) -> bidirect_check ctx e ty) estys in
        (Tu es) #: (Some ty)
    | Lam { lamarg; lambody }, Ty_arrow (label, t1, t2) ->
        let _ = _check_equality __FILE__ __LINE__ Leff.eq label None in
        let lamarg = _unify_update __FILE__ __LINE__ t1 lamarg in
        let ctx' = Typectx.new_to_right ctx (force_typed lamarg) in
        let lambody = bidirect_check ctx' lambody t2 in
        (Lam { lamarg; lambody }) #: (Some ty)
    | App (f, args), ty ->
        let f, fty = bidirect_infer ctx f in
        let argsty, retty = _solve_by_retty __FILE__ __LINE__ fty ty in
        let f' =
          bidirect_check ctx f (NTyped.construct_normal_tp (argsty, retty))
        in
        let argsargsty = _safe_combine __FILE__ __LINE__ args argsty in
        let args =
          List.map (fun (e, ty) -> bidirect_check ctx e ty) argsargsty
        in
        (App (f', args)) #: (Some ty)
    | Let { if_rec; lhs; rhs; letbody }, _ ->
        let xsty = List.map (fun x -> x.ty) lhs in
        let rhsty =
          match xsty with
          | [] ->
              _failatwith __FILE__ __LINE__ "infer: let binding lhs is empty"
          | [ Some tp ] -> tp
          | _ -> (
              match mk_tuple xsty with
              | None ->
                  _failatwith __FILE__ __LINE__ "infer: let binding lhs is none"
              | Some ty -> ty)
        in
        let rhs =
          match (if_rec, lhs) with
          | true, [ self ] ->
              let ctx' = Typectx.new_to_right ctx (force_typed self) in
              bidirect_check ctx' rhs rhsty
          | true, _ -> _failatwith __FILE__ __LINE__ "infer: bad let rec"
          | false, _ -> bidirect_check ctx rhs rhsty
        in
        let ctx' = Typectx.new_to_rights ctx @@ List.map force_typed lhs in
        let letbody = bidirect_check ctx' letbody ty in
        (Let { if_rec; lhs; rhs; letbody }) #: (Some ty)
    | Ite (e1, e2, e3), _ ->
        let e1 = bidirect_check ctx e1 Ty_bool in
        let e2 = bidirect_check ctx e2 ty in
        let e3 = bidirect_check ctx e3 ty in
        (Ite (e1, e2, e3)) #: (Some ty)
    | Match (_, []), _ ->
        _failatwith __FILE__ __LINE__ "infer: pattern matching branch is empty"
    | Match (e, cases), _ ->
        let e, ety = bidirect_infer ctx e in
        let handle_case { constructor; args; exp } =
          let constructor =
            _unify_update __FILE__ __LINE__
              (infer_op topctx constructor.x)
              constructor
          in
          let c = force_typed constructor in
          let argsty, retty =
            _solve_by_retty __FILE__ __LINE__ c.NTyped.ty ety
          in
          let constructor =
            constructor.x #: (Some (NTyped.construct_normal_tp (argsty, retty)))
          in
          let args =
            List.map (fun (x, ty) -> _unify_update __FILE__ __LINE__ ty x)
            @@ _safe_combine __FILE__ __LINE__ args argsty
          in
          let ctx' = Typectx.new_to_rights ctx (List.map force_typed args) in
          let exp = bidirect_check ctx' exp ty in
          let case = { constructor; args; exp } in
          case
        in
        (Match (e, List.map handle_case cases)) #: (Some ty)
    | _, _ ->
        _failatwith __FILE__ __LINE__
          (spf "check: inconsistent term (%s) and type (%s)"
             (layout x #: None)
             (NTyped.layout ty))
  and check_ret_case (ctx : Typectx.ctx) { retarg; retbody } (argty, retty) =
    let retarg = _unify_update __FILE__ __LINE__ argty retarg in
    let retbody = bidirect_check ctx retbody retty in
    { retarg; retbody }
  and check_handler_case (ctx : Typectx.ctx) { effop; effargs; effk; hbody }
      argty =
    let opty = infer_op topctx (Pmop.DtConstructor effop.x) in
    let effop = _unify_update __FILE__ __LINE__ opty effop in
    let opargsty, opretty = NTyped.destruct_arr_tp opty in
    let effk =
      _unify_update __FILE__ __LINE__ (NTyped.mk_arr opretty argty) effk
    in
    let effargs =
      List.map (fun (x, ty) -> _unify_update __FILE__ __LINE__ ty x)
      @@ _safe_combine __FILE__ __LINE__ effargs opargsty
    in
    let hbody = bidirect_check ctx hbody argty in
    { effop; effargs; effk; hbody }
  and infer_hd (ctx : Typectx.ctx) hd =
    let hdty =
      match hd.ty with
      | None -> _failatwith __FILE__ __LINE__ "hd should be typed"
      | Some hdty -> hdty
    in
    let { ret_case; handler_cases } = hd.x in
    let argty = NTyped.get_argty hdty in
    let retty = NTyped.get_retty hdty in
    let ret_case = check_ret_case ctx ret_case (argty, retty) in
    let handler_cases =
      List.map (fun x -> check_handler_case ctx x argty) handler_cases
    in
    ({ ret_case; handler_cases } #: (Some hdty), hdty)
  and infer (ctx : Typectx.ctx) (x : term) : term typed * NTyped.t =
    let x, ty =
      match x with
      | Err ->
          failwith
            "Cannot infer the type of the exception, should provide the return \
             type"
      | Const c -> (x, infer_const_ty topctx c)
      | Var id -> (x, infer_id topctx ctx id)
      | Tu es ->
          let es, esty = List.split @@ List.map (bidirect_infer ctx) es in
          (Tu es, NTyped.mk_tuple esty)
      | VHd hd ->
          let hd, hdty = infer_hd ctx hd in
          (VHd hd, hdty)
      | Lam { lamarg; lambody } ->
          let ctx' = Typectx.new_to_right ctx (force_typed lamarg) in
          let lambody, lambodyty = bidirect_infer ctx' lambody in
          let ty = NTyped.mk_arr (force_typed lamarg).NTyped.ty lambodyty in
          (Lam { lamarg; lambody }, ty)
      | Perform { rhsop; rhsargs } ->
          let rhsargs, argsty =
            List.split @@ List.map (bidirect_infer ctx) rhsargs
          in
          let argsty, retty =
            _solve_by_argsty __FILE__ __LINE__
              (infer_op topctx (Pmop.DtConstructor rhsop.x))
              argsty
          in
          let rhsop =
            _unify_update __FILE__ __LINE__
              (NTyped.construct_normal_tp (argsty, retty))
              rhsop
          in
          let rhsargs =
            List.map (fun (arg, ty) -> arg.x #: (Some ty))
            @@ _safe_combine __FILE__ __LINE__ rhsargs argsty
          in
          (Perform { rhsop; rhsargs }, retty)
      | AppOp (op, args) ->
          let args, argsty = List.split @@ List.map (bidirect_infer ctx) args in
          let argsty, retty =
            _solve_by_argsty __FILE__ __LINE__ (infer_op topctx op.x) argsty
          in
          let op =
            _unify_update __FILE__ __LINE__
              (NTyped.construct_normal_tp (argsty, retty))
              op
          in
          let args =
            List.map (fun (arg, ty) -> arg.x #: (Some ty))
            @@ _safe_combine __FILE__ __LINE__ args argsty
          in
          (AppOp (op, args), retty)
      | CWithH { handler; handled_prog } ->
          let handler, hdty = infer_hd ctx handler in
          let argty = NTyped.get_argty hdty in
          let retty = NTyped.get_retty hdty in
          let handled_prog = bidirect_check ctx handled_prog argty in
          (CWithH { handler; handled_prog }, retty)
      | App (f, args) ->
          let args, argsty =
            List.split @@ List.map (fun e -> bidirect_infer ctx e) args
          in
          let f, fty = bidirect_infer ctx f in
          let argsty, retty = _solve_by_argsty __FILE__ __LINE__ fty argsty in
          let f =
            bidirect_check ctx f (NTyped.construct_normal_tp (argsty, retty))
          in
          let args =
            List.map (fun (e, ty) -> bidirect_check ctx e ty)
            @@ _safe_combine __FILE__ __LINE__ args argsty
          in
          (App (f, args), retty)
      | Let { if_rec; _ } when if_rec ->
          _failatwith __FILE__ __LINE__
            "cannot infer ret type of recursive function"
      | Let { if_rec; lhs; rhs; letbody } ->
          let xsty = List.map (fun x -> x.ty) lhs in
          let rhsty =
            match xsty with
            | [] ->
                _failatwith __FILE__ __LINE__ "infer: let binding lhs is empty"
            | [ Some tp ] -> tp
            | _ -> (
                match mk_tuple xsty with
                | None ->
                    _failatwith __FILE__ __LINE__
                      "infer: let binding lhs is none"
                | Some ty -> ty)
          in
          let rhs =
            match (if_rec, lhs) with
            | true, [ self ] ->
                let ctx' = Typectx.new_to_right ctx (force_typed self) in
                bidirect_check ctx' rhs rhsty
            | true, _ -> _failatwith __FILE__ __LINE__ "infer: bad let rec"
            | false, _ -> bidirect_check ctx rhs rhsty
          in
          let ctx' = Typectx.new_to_rights ctx @@ List.map force_typed lhs in
          let letbody, ty = bidirect_infer ctx' letbody in
          (Let { if_rec; lhs; rhs; letbody }, ty)
      | Ite (e1, e2, e3) ->
          let e1 = bidirect_check ctx e1 Ty_bool in
          let e2, ty = bidirect_infer ctx e2 in
          let e3 = bidirect_check ctx e3 ty in
          (Ite (e1, e2, e3), ty)
      | Match (_, []) ->
          _failatwith __FILE__ __LINE__
            "infer: pattern matching branch is empty"
      | Match (e, cases) ->
          let e, ety = bidirect_infer ctx e in
          let handle_case { constructor; args; exp } =
            let constructor =
              _unify_update __FILE__ __LINE__
                (infer_op topctx constructor.x)
                constructor
            in
            let c = force_typed constructor in
            let argsty, retty =
              _solve_by_retty __FILE__ __LINE__ c.NTyped.ty ety
            in
            let constructor =
              constructor.x
              #: (Some (NTyped.construct_normal_tp (argsty, retty)))
            in
            let args =
              List.map (fun (x, ty) -> _unify_update __FILE__ __LINE__ ty x)
              @@ _safe_combine __FILE__ __LINE__ args argsty
            in
            let ctx' = Typectx.new_to_rights ctx (List.map force_typed args) in
            let exp, expty = bidirect_infer ctx' exp in
            let case = { constructor; args; exp } in
            (case, expty)
          in
          let cases, exptys = List.split @@ List.map handle_case cases in
          let ty =
            match exptys with
            | [] -> _failatwith __FILE__ __LINE__ "die"
            | ty :: t ->
                List.fold_left
                  (fun ty ty' -> NTyped._type_unify __FILE__ __LINE__ ty ty')
                  ty t
          in
          (Match (e, cases), ty)
    in
    (x #: (Some ty), ty)
  in
  match tyopt with
  | None -> fst (bidirect_infer Typectx.empty x)
  | Some ty -> bidirect_check Typectx.empty x ty

let struc_infer ctx l =
  Structure.map_imps
    (fun x if_rec body ->
      let rec get_fty e =
        match e.x with
        | Lam { lamarg; lambody } ->
            Sugar.(
              let* bty = get_fty lambody in
              let* aty = lamarg.ty in
              Some (NTyped.Ty_arrow (None, aty, bty)))
        | _ -> e.ty
      in
      match (if_rec, get_fty body) with
      | _, None ->
          _failatwith __FILE__ __LINE__
            "require the return type of the function"
      | false, ty -> type_check ctx body ty
      | true, Some ty ->
          type_check Typectx.(new_to_right ctx { x; ty }) body (Some ty))
    l
