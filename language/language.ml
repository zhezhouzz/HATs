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
end

module OptTypedTermlang = struct
  include Ast.OptTypedTermlang

  let layout = To_expr.layout
end

module Structure = struct
  include Ast.StructureRaw
end

module NTypectx = struct
  include Ast.NTypectx
end

(* unwrap *)
module Const = Ast.Const
module Pmop = Ast.Pmop
module Type_dec = Ast.Type_dec
