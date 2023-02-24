module type T = sig
  type t [@@deriving sexp]
end

module Ty = struct
  type t =
    | TyUnit
    | TyInt
    | TyArr of t * t
    | TyEffArr of t * t
    | TyHdArr of t * t
  [@@deriving sexp]
end

module OptTy = struct
  open Sexplib.Std

  type t = Ty.t option [@@deriving sexp]
end
