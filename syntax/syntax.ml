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

(* unwrap *)
module GMap = Minterm.GMap
module NRegex = Nregex.T
module Const = Constant
module Op = Op
module Type_dec = Type_dec
module Typectx = Typectx
module Corelang = Corelang
module Qn = Qn
