(* parsing only *)
module OptNt = Lit.OptTy
module LRaw = Lit.LitRaw
module StructureRaw = Structure.F (LRaw)
module RtyRaw = StructureRaw.R
module LRtyRaw = StructureRaw.LR
(* module QualifierRaw = RtyRaw.P *)

module Nt = Lit.Ty
module L = Lit.Lit
module Structure = Structure.F (L)
module Rty = Structure.R

module TypedCorelang = struct
  include Corelang.F (L)
end

(* module Qualifier = Rty.P *)

(* unwrap *)
(* module GMap = Minterm.GMap *)
module NRegex = Nregex.T
module Const = Constant
module Op = Op
module Type_dec = Type_dec
module Typectx = Typectx
module Corelang = Corelang
module Qn = Qn
