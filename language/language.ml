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

  let layout_rty = To_rty.layout
  let layout_entry = To_structure.layout_entry
  let layout = To_structure.layout
end

module RtyRaw = struct
  include Ast.RtyRaw

  let layout = To_rty.layout
end

module Rty = struct
  include Ast.Rty

  let layout rty = RtyRaw.layout (To_typed_rty.to_opt_rty rty)
  let force_typed_rty = To_typed_rty.force_typed_rty
  let to_opt_rty = To_typed_rty.to_opt_rty

  open Sugar

  let layout_typed f { x; ty } = spf "%s: %s" (f x) (layout ty)

  let layout_typed_l f l =
    Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l
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

module RTypectx = struct
  include Ast.Typectx.F (Rty)
  include Rty

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        | Mps _ | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty))
      code

  let from_code code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> Some name #: rty | RtyToCheck -> None)
      code

  let get_task code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> None | RtyToCheck -> Some (name, rty))
      code
end

module RTypedTermlang = struct
  include Ast.TypedTermlang

  let layout x = To_expr.layout @@ To_typed.to_opttyped_term x
end

module RTypedCoreEff = struct
  include Ast.Corelang.F (Rty)
end

(* unwrap *)
module Const = Ast.Const
module Pmop = Ast.Pmop
module Type_dec = Ast.Type_dec
