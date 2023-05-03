module NTyped = Lit.Ty
module OptTy = Lit.OptTy
module L = Lit.Lit
module LRaw = Lit.LitRaw
module TypedCoreEff = Corelang.F (NTyped)
module TypedTermlang = Termlang.F (NTyped)

module OptTypedCoreEff = struct
  include Corelang.F (LRaw)
end

module OptTypedTermlang = struct
  include Termlang.F (LRaw)
  (* open Sugar *)

  let de_typed_tuple { x; ty } = match x with Tu es -> es | _ -> [ { x; ty } ]
end

module StructureRaw = Structure.F (LRaw)
module Structure = Structure.F (L)
module RtyRaw = StructureRaw.R
module Rty = Structure.R
module QualifierRaw = RtyRaw.P

module NTypectx = struct
  include Typectx.F (Id.Id) (NTyped)
  include NTyped
end

module Equation = Algebraic.F (L)
module EquationRaw = Algebraic.F (LRaw)

module Eqctx = struct
  include Typectx.F (Id.Id) (Equation)
  include Equation
end

(* unwrap *)
module Const = Constant
module Op = Op
module Type_dec = Type_dec
module Typectx = Typectx
module Corelang = Corelang
