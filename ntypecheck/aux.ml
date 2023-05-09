open Language

(* open Const *)
module Ctx = NTypectx
module OpCtx = NOpTypectx
open Nt
open Sugar

let infer_id nctx x = Ctx.get_ty nctx x
let is_builtop opctx x = OpCtx.exists opctx (Op.BuiltinOp x)
let infer_const_ty _ = Const.infer_const_ty

let infer_op opctx x =
  match x with
  | Op.BuiltinOp _ ->
      (* let () = Printf.printf "infer op %s: %s\n" "BuiltinOp" op in *)
      (* let () = *)
      (*   Printf.printf "%s\n" (NOpTypectx.layout_typed_l Op.to_string opctx) *)
      (* in *)
      OpCtx.get_ty opctx x
  | Op.EffOp _ ->
      (* let () = Printf.printf "infer op %s: %s\n" "EffOp" op in *)
      OpCtx.get_ty opctx x
  | Op.DtOp x -> (
      match x with
      | "S" -> Ty_arrow (Ty_int, Ty_int)
      | _ ->
          _failatwith __FILE__ __LINE__
          @@ spf "cannot infer the basic type of %s" x)

open OptNt
open Zzdatatype.Datatype

let _unify = _type_unify
let _unify_ = Nt._type_unify_

let _unify_update file line ty' { x; ty } =
  x #: (_unify file line ty (Some ty'))

let infer_op_may_eff opctx op =
  match op.x with
  | Op.DtOp x -> (
      match OpCtx.get_ty_opt opctx (Op.EffOp x) with
      | Some ty -> ({ x = Op.EffOp x; ty = op.ty }, ty)
      | None ->
          let ty = OpCtx.get_ty opctx (Op.DtOp x) in
          ({ x = Op.DtOp x; ty = op.ty }, ty))
  | Op.BuiltinOp _ ->
      let ty = OpCtx.get_ty opctx op.x in
      (op, ty)
  | _ ->
      _failatwith __FILE__ __LINE__
        (spf "cannot infer the type of operator %s" (Op.to_string op.x))

let check_id nctx (x : string typed) : string typed * Nt.t =
  let ty = infer_id nctx x.x in
  (_unify_update __FILE__ __LINE__ ty x, ty)

let check_op opctx (x : Op.t typed) : Op.t typed * Nt.t =
  let ty = infer_op opctx x.x in
  (_unify_update __FILE__ __LINE__ ty x, ty)

let _solve_by_retty file line fty retty' =
  let open Nt in
  let argsty, retty = destruct_arr_tp fty in
  let m, retty = _unify_ file line StrMap.empty retty retty' in
  let subst m t =
    let rec aux t =
      match t with
      | Ty_var n -> (
          match StrMap.find_opt m n with None -> t | Some ty -> ty)
      | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
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
