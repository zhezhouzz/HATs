open Language
open Const
module Ctx = NTypectx
open Nt
open Sugar

let rec infer_const_ty topctx = function
  | U -> unit_ty
  | I _ -> int_ty
  | B _ -> bool_ty
  | Tu vs -> mk_tuple (List.map (infer_const_ty topctx) vs)
  | Dt (_, _) -> _failatwith __FILE__ __LINE__ "no dt const"
(* snd @@ destruct_arr_tp (infer_op topctx op) *)

let infer_id topctx ctx x =
  match Ctx.get_ty_opt ctx x with Some ty -> ty | None -> Ctx.get_ty topctx x

let infer_op topctx x =
  match x with
  | Op.BuiltinOp op -> Ctx.get_ty topctx op
  | Op.EffOp op -> Ctx.get_ty topctx op
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

let check_id topctx (x : string typed) : string typed * Nt.t =
  let ty = Ctx.get_ty topctx x.x in
  (_unify_update __FILE__ __LINE__ ty x, ty)
