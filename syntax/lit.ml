module type T = sig
  include Typed.T

  type lit =
    | AC of Constant.t
    | AVar of string
    | ATu of lit typed list
    | AProj of lit typed * int
    | AAppOp of Op.t typed * lit typed list

  val mk_lit_true : lit
  val mk_lit_false : lit
  val subst_lit : string * lit -> lit -> lit
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  module T = Ty
  include Ty

  type lit =
    | AC of Constant.t
    | AVar of string
    | ATu of lit typed list
    | AProj of lit typed * int
    | AAppOp of Op.t typed * lit typed list

  let mk_lit_true = AC (Constant.B true)
  let mk_lit_false = AC (Constant.B false)

  let subst_lit (y, lit) e =
    let rec aux e =
      match e with
      | AC _ -> e
      | AVar x -> if String.equal x y then lit else e
      | ATu ls -> ATu (List.map (fun x -> aux #-> x) ls)
      | AProj (l, idx) -> AProj (aux #-> l, idx)
      | AAppOp (op, ls) -> AAppOp (op, List.map (fun x -> aux #-> x) ls)
    in
    aux e
end

module Ty = struct
  include Normalty.Ntyped
end

module OptTy = struct
  include Normalty.NOpttyped
end

module LitRaw = F (OptTy)
module Lit = F (Ty)
