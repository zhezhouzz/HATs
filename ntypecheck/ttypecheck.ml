open Language
open Zzdatatype.Datatype
open Sugar
open StructureRaw
open Aux
(* module L = TypedTermlang *)

let _partial_curry file line n arrty =
  let open Nt in
  let args, ret = destruct_arr_tp arrty in
  if n > List.length args then
    _failatwith file line (spf "_partial_curry(%i): %s" n (layout arrty))
  else
    let args1 = List.sublist args ~start_included:0 ~end_excluded:n in
    let args2 =
      List.sublist args ~start_included:n ~end_excluded:(List.length args)
    in
    (args1, construct_arr_tp (args2, ret))

let _solve_by_argsty file line fty argsty' =
  let open Nt in
  (* let () = *)
  (*   Printf.printf "[%s(%i)]: fty: %s; argsty': %s\n" file line (layout fty) *)
  (*     (List.split_by_comma layout argsty') *)
  (* in *)
  let argsty, retty = _partial_curry file line (List.length argsty') fty in
  (* let () = *)
  (*   Printf.printf "[%s(%i)]: argsty: %s; retty: %s\n" file line *)
  (*     (List.split_by_comma layout argsty) *)
  (*     (layout retty) *)
  (* in *)
  let m, argsty_ =
    _type_unify_ file line StrMap.empty (mk_tuple argsty) (mk_tuple argsty')
  in
  let argsty =
    match argsty_ with Ty_tuple argsty -> argsty | t -> [ t ]
    (* | _ -> _failatwith __FILE__ __LINE__ (spf "? <%s>" (layout argsty_)) *)
  in
  let retty = subst_m m retty in
  (argsty, retty)

let destruct_by_uncurry_ret file line fty retty' =
  let open Nt in
  let b1, _ = destruct_arr_tp retty' in
  let a1, _ = destruct_arr_tp fty in
  _partial_curry file line (List.length a1 - List.length b1) fty

let _solve_by_retty file line fty retty' =
  let open Nt in
  let argsty, retty = destruct_by_uncurry_ret file line fty retty' in
  let m, retty = _unify_ file line StrMap.empty retty retty' in
  let subst m t =
    let rec aux t =
      match t with
      | Ty_var n -> (
          match StrMap.find_opt m n with None -> t | Some ty -> ty)
      (* | Ty_list t -> Ty_list (aux t) *)
      | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
      | Ty_tuple ts -> Ty_tuple (List.map aux ts)
      | Ty_constructor (id, ts) -> Ty_constructor (id, List.map aux ts)
      | _ -> t
    in
    aux t
  in
  let argsty = List.map (subst m) argsty in
  (argsty, retty)

let type_check (opctx : NOpTypectx.ctx) (nctx : NTypectx.ctx) (x : term typed)
    (tyopt : t) : term typed =
  let rec bidirect_infer (ctx : NTypectx.ctx) (x : term typed) :
      term typed * Nt.t =
    match x.ty with None -> infer ctx x.x | Some ty -> (check ctx x.x ty, ty)
  and bidirect_check (ctx : NTypectx.ctx) (x : term typed) (ty : Nt.t) :
      term typed =
    match x.ty with
    | None -> check ctx x.x ty
    | Some ty' ->
        let ty = Nt._type_unify __FILE__ __LINE__ ty' ty in
        check ctx x.x ty
  and check (ctx : NTypectx.ctx) (x : term) (ty : Nt.t) : term typed =
    let () =
      Env.show_debug_preprocess @@ fun _ ->
      Ctx.pretty_print_judge ctx (layout_term x #: None, ty)
    in
    match (x, ty) with
    | Err, _ -> Err #: (Some ty)
    | Const _, _ | Var _, _ | AppOp (_, _), _ ->
        let x, _ = infer ctx x in
        _unify_update __FILE__ __LINE__ ty x
    | Tu es, Ty_tuple tys ->
        let estys = _safe_combine __FILE__ __LINE__ es tys in
        let es = List.map (fun (e, ty) -> bidirect_check ctx e ty) estys in
        (Tu es) #: (Some ty)
    | Lam { lamarg; lambody }, Ty_arrow (t1, t2) ->
        let lamarg = _unify_update __FILE__ __LINE__ t1 lamarg in
        let ctx' =
          NTypectx.new_to_right ctx (Coersion.force __FILE__ __LINE__ lamarg)
        in
        let lambody = bidirect_check ctx' lambody t2 in
        (Lam { lamarg; lambody }) #: (Some ty)
    | App (f, args), ty -> (
        match f.x with
        | Var x when is_builtop opctx x ->
            check ctx (AppOp ({ x = Op.BuiltinOp x; ty = f.ty }, args)) ty
        | _ ->
            let f, fty = bidirect_infer ctx f in
            (* let () = Printf.printf "F: %s\n" (layout f) in *)
            (* let () = Printf.printf "ty: %s\n" (Nt.layout ty) in *)
            let argsty, retty = _solve_by_retty __FILE__ __LINE__ fty ty in
            let f' =
              bidirect_check ctx f (Nt.construct_arr_tp (argsty, retty))
            in
            let argsargsty = _safe_combine __FILE__ __LINE__ args argsty in
            let args =
              List.map (fun (e, ty) -> bidirect_check ctx e ty) argsargsty
            in
            (App (f', args)) #: (Some ty))
    | Let { if_rec; lhs; rhs; letbody }, _ ->
        let xsty = List.map (fun x -> x.ty) lhs in
        (* let () = *)
        (*   Printf.printf "lhs = %s; rhs = %s; letbody = %s\n" *)
        (*     (layout_typed_l (fun x -> x) lhs) *)
        (*     (layout rhs) (layout letbody) *)
        (* in *)
        let rhsty =
          match xsty with
          | [] ->
              _failatwith __FILE__ __LINE__ "infer: let binding lhs is empty"
          | [ Some tp ] -> tp
          | _ -> (
              match mk_tuple xsty with
              | None ->
                  _failatwith __FILE__ __LINE__
                    "infer: let binding lhs is not typed"
              | Some ty -> ty)
        in
        let rhs =
          match (if_rec, lhs) with
          | true, [ self ] ->
              let ctx' =
                NTypectx.new_to_right ctx
                  (Coersion.force __FILE__ __LINE__ self)
              in
              bidirect_check ctx' rhs rhsty
          | true, _ -> _failatwith __FILE__ __LINE__ "infer: bad let rec"
          | false, _ -> bidirect_check ctx rhs rhsty
        in
        let ctx' =
          NTypectx.new_to_rights ctx
          @@ List.map (Coersion.force __FILE__ __LINE__) lhs
        in
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
              (infer_op opctx Op.(DtOp constructor.x))
              constructor
          in
          let c = Coersion.force __FILE__ __LINE__ constructor in
          let argsty, retty = _solve_by_retty __FILE__ __LINE__ c.Nt.ty ety in
          let constructor =
            constructor.x #: (Some (Nt.construct_arr_tp (argsty, retty)))
          in
          let args =
            List.map (fun (x, ty) -> _unify_update __FILE__ __LINE__ ty x)
            @@ _safe_combine __FILE__ __LINE__ args argsty
          in
          let ctx' =
            NTypectx.new_to_rights ctx
              (List.map (Coersion.force __FILE__ __LINE__) args)
          in
          let exp = bidirect_check ctx' exp ty in
          let case = { constructor; args; exp } in
          case
        in
        (Match (e, List.map handle_case cases)) #: (Some ty)
    | _, _ ->
        _failatwith __FILE__ __LINE__
          (spf "check: inconsistent term (%s) and type (%s)"
             (layout_term x #: None)
             (Nt.layout ty))
  and infer (ctx : NTypectx.ctx) (x : term) : term typed * Nt.t =
    let x, ty =
      match x with
      | Err ->
          failwith
            "Cannot infer the type of the exception, should provide the return \
             type"
      | Const c -> (x, infer_const_ty opctx c)
      | Var id -> (x, infer_id ctx id)
      | Tu es ->
          let es, esty = List.split @@ List.map (bidirect_infer ctx) es in
          (Tu es, Nt.mk_tuple esty)
      | Lam { lamarg; lambody } ->
          let ctx' =
            NTypectx.new_to_right ctx (Coersion.force __FILE__ __LINE__ lamarg)
          in
          let lambody, lambodyty = bidirect_infer ctx' lambody in
          let ty =
            Nt.mk_arr (Coersion.force __FILE__ __LINE__ lamarg).Nt.ty lambodyty
          in
          (Lam { lamarg; lambody }, ty)
      | AppOp (op, args) ->
          let args, argsty = List.split @@ List.map (bidirect_infer ctx) args in
          let op, opty = infer_op_may_eff opctx op in
          let argsty, retty = _solve_by_argsty __FILE__ __LINE__ opty argsty in
          let op =
            _unify_update __FILE__ __LINE__
              (Nt.construct_arr_tp (argsty, retty))
              op
          in
          let args =
            List.map (fun (arg, ty) -> arg.x #: (Some ty))
            @@ _safe_combine __FILE__ __LINE__ args argsty
          in
          (AppOp (op, args), retty)
      | App (f, args) -> (
          match f.x with
          | Var x when is_builtop opctx x ->
              let x, ty =
                infer ctx (AppOp ({ x = Op.BuiltinOp x; ty = f.ty }, args))
              in
              (x.x, ty)
          | _ ->
              let f, fty = bidirect_infer ctx f in
              let args, argsty =
                List.split @@ List.map (fun e -> bidirect_infer ctx e) args
              in
              let argsty, retty =
                _solve_by_argsty __FILE__ __LINE__ fty argsty
              in
              let f =
                bidirect_check ctx f (Nt.construct_arr_tp (argsty, retty))
              in
              let args =
                List.map (fun (e, ty) -> bidirect_check ctx e ty)
                @@ _safe_combine __FILE__ __LINE__ args argsty
              in
              (App (f, args), retty))
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
                let ctx' =
                  NTypectx.new_to_right ctx
                    (Coersion.force __FILE__ __LINE__ self)
                in
                bidirect_check ctx' rhs rhsty
            | true, _ -> _failatwith __FILE__ __LINE__ "infer: bad let rec"
            | false, _ -> bidirect_check ctx rhs rhsty
          in
          let ctx' =
            NTypectx.new_to_rights ctx
            @@ List.map (Coersion.force __FILE__ __LINE__) lhs
          in
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
                (infer_op opctx Op.(DtOp constructor.x))
                constructor
            in
            let c = Coersion.force __FILE__ __LINE__ constructor in
            let argsty, retty = _solve_by_retty __FILE__ __LINE__ c.Nt.ty ety in
            let constructor =
              constructor.x #: (Some (Nt.construct_arr_tp (argsty, retty)))
            in
            let args =
              List.map (fun (x, ty) -> _unify_update __FILE__ __LINE__ ty x)
              @@ _safe_combine __FILE__ __LINE__ args argsty
            in
            let ctx' =
              NTypectx.new_to_rights ctx
                (List.map (Coersion.force __FILE__ __LINE__) args)
            in
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
                  (fun ty ty' -> Nt._type_unify __FILE__ __LINE__ ty ty')
                  ty t
          in
          (Match (e, cases), ty)
    in
    let () =
      Env.show_debug_preprocess @@ fun _ ->
      Ctx.pretty_print_infer ctx (layout_term x #: None, ty)
    in
    (x #: (Some ty), ty)
  in
  match tyopt with
  | None -> fst (bidirect_infer nctx x)
  | Some ty -> bidirect_check nctx x ty
