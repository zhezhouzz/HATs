(* parsing only *)
module OptNt = Lit.OptTy
module LRaw = Lit.LitRaw
module StructureRaw = Structure.F (LRaw)
module RtyRaw = StructureRaw.R
(* module QualifierRaw = RtyRaw.P *)

(* module OptTypedCoreEff = struct *)
(*   include Corelang.F (LRaw) *)
(* end *)

module Nt = Lit.Ty
module L = Lit.Lit
module Structure = Structure.F (L)
module Rty = Structure.R

(* module Qualifier = Rty.P *)
module Equation = Algebraic.F (L)
module EquationRaw = Algebraic.F (LRaw)

module Eqctx = struct
  include Typectx.F (Equation)
  include Equation
end

module TypedCoreEff = Corelang.F (Nt)

(* unwrap *)
module Const = Constant
module Op = Op
module Type_dec = Type_dec
module Typectx = Typectx
module Corelang = Corelang
