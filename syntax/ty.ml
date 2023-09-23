module type T = sig
  type t [@@deriving sexp]

  val eq : t -> t -> bool
  val default_ty : t
  val unit_ty : t
  val int_ty : t
  val bool_ty : t
  val mk_arr : t -> t -> t
  val mk_effarr : t -> t -> t
  val mk_hdarr : t -> t -> t
  val get_argty : t -> t
  val get_retty : t -> t
end

module Ty = struct
  type t =
    | TyAny
    | TyUnit
    | TyInt
    | TyBool
    | TyArr of t * t
    | TyEffArr of t * t
    | TyHdArr of t * t
  [@@deriving sexp]

  let eq x y =
    let rec aux (x, y) =
      match (x, y) with
      | TyAny, TyAny | TyUnit, TyUnit | TyBool, TyBool | TyInt, TyInt -> true
      | TyArr (x, x'), TyArr (y, y') -> aux (x, y) && aux (x', y')
      | TyEffArr (x, x'), TyEffArr (y, y') -> aux (x, y) && aux (x', y')
      | TyHdArr (x, x'), TyHdArr (y, y') -> aux (x, y) && aux (x', y')
      | _, _ -> false
    in
    aux (x, y)

  let default_ty = TyUnit
  let unit_ty = TyUnit
  let int_ty = TyInt
  let bool_ty = TyBool
  let mk_arr t1 t2 = TyArr (t1, t2)
  let mk_effarr t1 t2 = TyEffArr (t1, t2)
  let mk_hdarr t1 t2 = TyHdArr (t1, t2)

  open Sugar

  let get_argty = function
    | TyArr (t1, _) -> t1
    | TyEffArr (t1, _) -> t1
    | TyHdArr (t1, _) -> t1
    | _ -> _failatwith __FILE__ __LINE__ "?"

  let get_retty = function
    | TyArr (_, t1) -> t1
    | TyEffArr (_, t1) -> t1
    | TyHdArr (_, t1) -> t1
    | _ -> _failatwith __FILE__ __LINE__ "?"
end

module OptTy = struct
  open Sexplib.Std

  type t = Ty.t option [@@deriving sexp]

  let default_ty = None
  let unit_ty = Some Ty.TyUnit
  let int_ty = Some Ty.TyInt
  let bool_ty = Some Ty.TyBool
  let some_ty (ty : Ty.t) : t = Some ty

  let eq x y =
    match (x, y) with
    | None, None -> true
    | Some x, Some y -> Ty.eq x y
    | _, _ -> false

  let mk_arr t1 t2 =
    match (t1, t2) with
    | Some t1, Some t2 -> Some (Ty.TyArr (t1, t2))
    | _ -> None

  let mk_effarr t1 t2 =
    match (t1, t2) with
    | Some t1, Some t2 -> Some (Ty.TyEffArr (t1, t2))
    | _ -> None

  let mk_hdarr t1 t2 =
    match (t1, t2) with
    | Some t1, Some t2 -> Some (Ty.TyHdArr (t1, t2))
    | _ -> None

  let get_argty = function Some t -> Some (Ty.get_argty t) | None -> None
  let get_retty = function Some t -> Some (Ty.get_retty t) | None -> None
end
