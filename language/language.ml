module Ty = struct
  include Ast.Ty
end

module OptTy = struct
  include Ast.OptTy
end

module TypedCoreEff = struct
  include Ast.TypedCoreEff
end

module OptTypedCoreEff = struct
  include Ast.OptTypedCoreEff
end

module TypedTermlang = struct
  include Ast.TypedTermlang

  let layout x = To_expr.layout @@ To_typed.to_opttyped_term x
end

module OptTypedTermlang = struct
  include Ast.OptTypedTermlang

  let layout = To_expr.layout
end

module StructureRaw = struct
  include Ast.StructureRaw

  let layout_entry = To_structure.layout_entry
  let layout = To_structure.layout
end

module Structure = struct
  include Ast.Structure

  let layout_entry x =
    To_structure.layout_entry @@ To_typed.to_opttyped_struct_one x

  let layout x = To_structure.layout @@ To_typed.to_opttyped_struct x
end

module NTypectx = struct
  include Ast.NTypectx
end

(* unwrap *)
module Const = Ast.Const
module Pmop = Ast.Pmop
module Type_dec = Ast.Type_dec
