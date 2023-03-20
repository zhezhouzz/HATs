open Language.Const
module Ty = Normalty.Ntyped
module Ctx = Language.NTypectx
module Op = Language.Pmop
(* open Normalty.NOpttyped *)

let infer_const_ty topctx = function
  | U -> Ty.unit_ty
  | I _ -> Ty.int_ty
  | B _ -> Ty.bool_ty
  | Prim name -> Ctx.get_ty topctx name

open Sugar

let infer_id topctx ctx x =
  match Ctx.get_ty_opt ctx x with
  | Some ty -> ty
  | None -> (
      match Ctx.get_ty_opt topctx x with
      | Some ty -> ty
      | None ->
          _failatwith __FILE__ __LINE__
          @@ spf "cannot infer the basic type of %s" x)

let infer_op topctx x =
  match x with
  | Op.External _ -> _failatwith __FILE__ __LINE__ "unimp"
  | Op.DtConstructor x -> (
      match Ctx.get_ty_opt topctx x with
      | Some ty -> ty
      | None ->
          _failatwith __FILE__ __LINE__
          @@ spf "cannot infer the basic type of %s" x)
