open Language
open Zzdatatype.Datatype
open Sugar
open RtyRaw.P
open Aux

let force_typed { x; ty } =
  match ty with
  | None -> _failatwith __FILE__ __LINE__ "?"
  | Some ty -> Nt.{ x; ty }

let rec type_infer_lit (opctx : NOpTypectx.ctx) (ctx : NTypectx.ctx) (lit : lit)
    : lit * Nt.t =
  match lit with
  | AC c -> (AC c, infer_const_ty ctx c)
  | AVar x ->
      let ty = infer_id ctx x in
      (AVar x, ty)
  | ATu l ->
      let l, tys =
        List.split
        @@ List.map
             (fun x ->
               let x, ty = type_infer_lit opctx ctx x.x in
               (x #: (Some ty), ty))
             l
      in
      (ATu l, Nt.mk_tuple tys)
  | AProj (a, n) -> (
      let x, aty = type_infer_lit opctx ctx a.x in
      let a = x #: (Some aty) in
      match aty with
      | Nt.Ty_tuple tys when n < List.length tys ->
          (AProj (a, n), List.nth tys n)
      | _ -> _failatwith __FILE__ __LINE__ "?")
  | AAppOp (f, args) ->
      let args, argsty =
        List.split
        @@ List.map
             (fun x ->
               let x, ty = type_infer_lit opctx ctx x.x in
               (x, ty))
             args
      in
      let f, fty =
        match (f.x, argsty) with
        | Op.BuiltinOp "==", [ t1; t2 ] when Nt.eq t1 t2 ->
            ({ x = f.x; ty = Some t1 }, Nt.(mk_arr t1 @@ mk_arr t1 Ty_bool))
        | _ -> check_op opctx f
      in
      let argsty, retty = _solve_by_argsty __FILE__ __LINE__ fty argsty in
      let args =
        List.map (type_check_lit opctx ctx)
          (_safe_combine __FILE__ __LINE__ args argsty)
      in
      (AAppOp (f, args), retty)

and type_check_lit (opctx : NOpTypectx.ctx) (ctx : NTypectx.ctx) (lit, ty) :
    lit typed =
  (* let () = *)
  (*   Printf.printf "Check %s <<= %s\n" *)
  (*     (To_qualifier.layout_lit lit) *)
  (*     (Nt.layout ty) *)
  (* in *)
  match lit with
  | AC _ | AVar _ ->
      let x, ty' = type_infer_lit opctx ctx lit in
      let ty = _check_equality __FILE__ __LINE__ Nt.eq ty ty' in
      { x; ty = Some ty }
  | ATu l ->
      let tys =
        match ty with
        | Nt.Ty_tuple tys -> tys
        | _ -> _failatwith __FILE__ __LINE__ "?"
      in
      let l =
        List.map
          (fun (x, ty) -> type_check_lit opctx ctx (x.x, ty))
          (_safe_combine __FILE__ __LINE__ l tys)
      in
      { x = ATu l; ty = Some (Nt.Ty_tuple tys) }
  | AProj (_, _) ->
      let lit, ty' = type_infer_lit opctx ctx lit in
      let ty = _check_equality __FILE__ __LINE__ Nt.eq ty ty' in
      { x = lit; ty = Some ty }
  | AAppOp (f, args) ->
      let args, argsty =
        List.split @@ List.map (fun x -> type_infer_lit opctx ctx x.x) args
      in
      (* let () = *)
      (*   Printf.printf ">> %s(%s)\n" (Op.to_string f.x) *)
      (*     (List.split_by_comma Nt.layout argsty) *)
      (* in *)
      let f, fty =
        match (f.x, argsty) with
        | Op.BuiltinOp "==", [ t1; t2 ] when Nt.eq t1 t2 ->
            ({ x = f.x; ty = Some t1 }, Nt.(mk_arr t1 @@ mk_arr t1 Ty_bool))
        | _ -> check_op opctx f
      in
      (* let () = Printf.printf ">> %s:%s\n" (Op.to_string f.x) (Nt.layout fty) in *)
      let argsty, retty = _solve_by_argsty __FILE__ __LINE__ fty argsty in
      let argsty, retty =
        _solve_by_retty __FILE__ __LINE__
          (Nt.construct_arr_tp (argsty, retty))
          ty
      in
      let f = f.x #: (Some (Nt.construct_arr_tp (argsty, retty))) in
      let args =
        List.map (type_check_lit opctx ctx)
          (_safe_combine __FILE__ __LINE__ args argsty)
      in
      { x = AAppOp (f, args); ty = Some retty }

let type_check_qualifier (opctx : NOpTypectx.ctx) (ctx : NTypectx.ctx)
    (qualifier : prop) : prop =
  let ty = Nt.bool_ty in
  let rec aux ctx qualifier =
    match qualifier with
    | Lit lit -> Lit (type_check_lit opctx ctx (lit, ty)).x
    | Implies (e1, e2) -> Implies (aux ctx e1, aux ctx e2)
    | Ite (e1, e2, e3) -> Ite (aux ctx e1, aux ctx e2, aux ctx e3)
    | Not e -> Not (aux ctx e)
    | And es -> And (List.map (aux ctx) es)
    | Or es -> Or (List.map (aux ctx) es)
    | Iff (e1, e2) -> Iff (aux ctx e1, aux ctx e2)
    | Forall (u, body) ->
        let ctx' = NTypectx.new_to_right ctx u in
        Forall (u, aux ctx' body)
    | Exists (u, body) ->
        let ctx' = NTypectx.new_to_right ctx u in
        Exists (u, aux ctx' body)
  in
  aux ctx qualifier
