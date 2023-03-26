open Language.Const
module Ty = Normalty.Ntyped
module Ctx = Language.NTypectx
module Op = Language.Pmop
open Sugar

let infer_op topctx x =
  match x with
  | Op.External _ -> _failatwith __FILE__ __LINE__ "unimp"
  | Op.DtConstructor x -> (
      match Ctx.get_ty_opt topctx x with
      | Some ty -> ty
      | None ->
          _failatwith __FILE__ __LINE__
          @@ spf "cannot infer the basic type of %s" x)

let rec infer_const_ty topctx = function
  | U -> Ty.unit_ty
  | I _ -> Ty.int_ty
  | B _ -> Ty.bool_ty
  | Tu vs -> Ty.mk_tuple (List.map (infer_const_ty topctx) vs)
  | Dt (op, _) -> snd @@ Ty.destruct_arr_tp (infer_op topctx op)

let infer_id topctx ctx x =
  match Ctx.get_ty_opt ctx x with
  | Some ty -> ty
  | None -> (
      match Ctx.get_ty_opt topctx x with
      | Some ty -> ty
      | None ->
          _failatwith __FILE__ __LINE__
          @@ spf "cannot infer the basic type of %s" x)
