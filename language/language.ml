module Ty = struct
  include Normalty.Ntyped
end

module OptTy = struct
  include Normalty.NOpttyped
end

module TypedCoreEff = Corelang.F (Ty)

module OptTypedCoreEff = struct
  include Corelang.F (OptTy)
end

module TypedTermlang = Termlang.F (Ty)

module OptTypedTermlang = struct
  include Termlang.F (OptTy)
  (* open Sugar *)

  let de_typed_tuple { x; ty } = match x with Tu es -> es | _ -> [ { x; ty } ]
end

(* unwrap *)
module Const = Constant
