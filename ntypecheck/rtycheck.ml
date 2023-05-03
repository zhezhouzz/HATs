open Language
module Typectx = NTypectx
open Zzdatatype.Datatype
open Sugar
module R = RtyRaw
open RtyRaw
module Nt = Normalty.Ntyped
open P

let _unify = _type_unify
let _unify_ = Nt._type_unify_

let _unify_update file line ty' { x; ty } =
  x #: (_unify file line ty (Some ty'))

let _solve_by_retty file line fty retty' =
  let open Nt in
  let argsty, retty = destruct_arr_tp fty in
  let m, retty = _unify_ file line StrMap.empty retty retty' in
  let subst m t =
    let rec aux t =
      match t with
      | Ty_var n -> (
          match StrMap.find_opt m n with None -> t | Some ty -> ty)
      (* | Ty_list t -> Ty_list (aux t) *)
      | Ty_arrow (l, t1, t2) -> Ty_arrow (l, aux t1, aux t2)
      | Ty_tuple ts -> Ty_tuple (List.map aux ts)
      | Ty_constructor (id, ts) -> Ty_constructor (id, List.map aux ts)
      | _ -> t
    in
    aux t
  in
  let argsty = List.map (subst m) argsty in
  (argsty, retty)

let _solve_by_argsty file line fty argsty' =
  let open Nt in
  let argsty, retty = destruct_arr_tp fty in
  let m, argsty_ =
    _type_unify_ file line StrMap.empty (mk_tuple argsty) (mk_tuple argsty')
  in
  let argsty = match argsty_ with Ty_tuple argsty -> argsty | t -> [ t ] in
  let retty = subst_m m retty in
  (argsty, retty)

let force_typed { x; ty } =
  match ty with
  | None -> _failatwith __FILE__ __LINE__ "?"
  | Some ty -> Nt.{ x; ty }

let type_infer_id (topctx : Typectx.ctx) (x : string typed) :
    string typed * Nt.t =
  let ty = Typectx.get_ty topctx x.x in
  (_unify_update __FILE__ __LINE__ ty x, ty)

let rec type_infer_lit (topctx : Typectx.ctx) (lit : P.lit) : P.lit * Nt.t =
  let open P in
  match lit with
  | AC c -> (AC c, Aux.infer_const_ty topctx c)
  | AVar x ->
      let x, ty = type_infer_id topctx x in
      (AVar x, ty)
  | ATu l ->
      let l, tys = List.split @@ List.map (type_infer_lit topctx) l in
      (ATu l, Nt.mk_tuple tys)
  | AProj (n, total, a) -> (
      let a, aty = type_infer_lit topctx a in
      match aty with
      | Nt.Ty_tuple tys when List.length tys == total && n < total ->
          (AProj (n, total, a), List.nth tys n)
      | _ -> _failatwith __FILE__ __LINE__ "?")
  | AApp (f, args) ->
      let args, argsty = List.split @@ List.map (type_infer_lit topctx) args in
      let f, fty = type_infer_id topctx f in
      let argsty, retty = _solve_by_argsty __FILE__ __LINE__ fty argsty in
      let args =
        List.map (type_check_lit topctx)
          (_safe_combine __FILE__ __LINE__ args argsty)
      in
      (AApp (f, args), retty)

and type_check_lit (topctx : Typectx.ctx) (lit, ty) : P.lit =
  let open P in
  (* let () = *)
  (*   Printf.printf "Check %s <<= %s\n" *)
  (*     (To_qualifier.layout_lit lit) *)
  (*     (Nt.layout ty) *)
  (* in *)
  match lit with
  | AC _ | AVar _ ->
      let lit, ty' = type_infer_lit topctx lit in
      let _ = _check_equality __FILE__ __LINE__ Nt.eq ty ty' in
      lit
  | ATu l ->
      let tys =
        match ty with
        | Nt.Ty_tuple tys -> tys
        | _ -> _failatwith __FILE__ __LINE__ "?"
      in
      ATu
        (List.map (type_check_lit topctx)
           (_safe_combine __FILE__ __LINE__ l tys))
  | AProj (n, total, a) ->
      let tys = List.init total (fun i -> if i == n then Nt.Ty_any else ty) in
      AProj (n, total, type_check_lit topctx (a, Nt.mk_tuple tys))
  | AApp (f, args) ->
      let args, argsty = List.split @@ List.map (type_infer_lit topctx) args in
      let f, fty = type_infer_id topctx f in
      (* let () = Printf.printf "%s:%s\n" f.x (Nt.layout fty) in *)
      let argsty, retty = _solve_by_argsty __FILE__ __LINE__ fty argsty in
      let argsty, retty =
        _solve_by_retty __FILE__ __LINE__
          (Nt.construct_normal_tp (argsty, retty))
          ty
      in
      let f = f.x #: (Some (Nt.construct_normal_tp (argsty, retty))) in
      let args =
        List.map (type_check_lit topctx)
          (_safe_combine __FILE__ __LINE__ args argsty)
      in
      AApp (f, args)

let type_check_qualifier (topctx : Typectx.ctx) (qualifier : P.t) : P.t =
  let open P in
  let ty = Nt.bool_ty in
  let rec aux topctx qualifier =
    match qualifier with
    | Lit lit -> Lit (type_check_lit topctx (lit, ty))
    | MethodPred (mp, args) ->
        let mp, fty = type_infer_id topctx mp in
        let argsty, retty = _solve_by_retty __FILE__ __LINE__ fty ty in
        let mp = mp.x #: (Some Nt.(construct_normal_tp (argsty, retty))) in
        let args =
          List.map (type_check_lit topctx)
            (_safe_combine __FILE__ __LINE__ args argsty)
        in
        MethodPred (mp, args)
    | Implies (e1, e2) -> Implies (aux topctx e1, aux topctx e2)
    | Ite (e1, e2, e3) -> Ite (aux topctx e1, aux topctx e2, aux topctx e3)
    | Not e -> Not (aux topctx e)
    | And es -> And (List.map (aux topctx) es)
    | Or es -> Or (List.map (aux topctx) es)
    | Iff (e1, e2) -> Iff (aux topctx e1, aux topctx e2)
    | Forall (u, body) ->
        let topctx' = Typectx.new_to_right topctx u in
        Forall (u, aux topctx' body)
    | Exists (u, body) ->
        let topctx' = Typectx.new_to_right topctx u in
        Exists (u, aux topctx' body)
  in
  aux topctx qualifier

let basety_check ctx { v; phi } =
  let ctx' = Typectx.new_to_rights ctx [ v ] in
  let phi = type_check_qualifier ctx' phi in
  { v; phi }

let type_check ctx (rty : R.t) : R.t =
  let rec aux ctx rty =
    match rty with
    | BaseRty { ou; basety } -> BaseRty { ou; basety = basety_check ctx basety }
    | Traced { h; pre; rty; post } ->
        let pre = basety_check ctx pre in
        let ctx' = Typectx.new_to_rights ctx [ Nt.(h #: (erase_basety pre)) ] in
        let post = basety_check ctx' post in
        let rty = aux ctx' rty in
        Traced { h; pre; rty; post }
    | DepRty { dep; label; rarg; retrty } ->
        let rarg = RtyRaw.{ x = rarg.x; ty = aux ctx rarg.ty } in
        let ctx' =
          match rarg.RtyRaw.x with
          | None -> ctx
          | Some x -> Typectx.new_to_right ctx Nt.(x #: (erase rarg.RtyRaw.ty))
        in
        let retrty = aux ctx' retrty in
        DepRty { dep; label; rarg; retrty }
  in
  aux ctx rty

let check_rty ctx (rty : R.t) : Rty.t = Rty.force_typed_rty (type_check ctx rty)
