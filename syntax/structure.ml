module F (L : Lit.T) = struct
  include Termlang.F (L)
  module R = Rty.F (L)

  type rty_kind = RtyLib | RtyToCheck

  type entry =
    (* | Mps of string list *)
    | Type_dec of Type_dec.t
    | Func_dec of string Normalty.Ntyped.typed
    | FuncImp of { name : string; if_rec : bool; body : term typed }
    | Rty of { name : string; kind : rty_kind; rty : R.rty }

  type structure = entry list

  (* open Sugar *)
  open Zzdatatype.Datatype

  let mk_normal_top_ctx_ = function
    | FuncImp _ -> []
    | Rty { name; kind; rty } -> (
        match kind with RtyLib -> [ (name, R.erase rty) ] | RtyToCheck -> [])
    | Func_dec x -> [ (x.x, x.ty) ]
    | Type_dec _ -> []

  let mk_normal_top_opctx_ = function
    | FuncImp _ -> []
    | Rty _ -> []
    | Func_dec _ -> []
    | Type_dec d ->
        List.map (fun R.Nt.{ x; ty } -> (x, ty)) @@ Type_dec.mk_ctx_ d

  let mk_normal_top_ctx es = List.concat @@ List.map mk_normal_top_ctx_ es
  let mk_normal_top_opctx es = List.concat @@ List.map mk_normal_top_opctx_ es

  let map_imps f codes =
    List.map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } ->
            FuncImp { name; if_rec; body = f name if_rec body }
        | _ -> code)
      codes

  let map_rtys f codes =
    List.map
      (fun code ->
        match code with
        | Rty { name; kind; rty } -> Rty { name; kind; rty = f rty }
        | _ -> code)
      codes

  let filter_map_imps f codes =
    List.filter_map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } -> f name if_rec body
        | _ -> None)
      codes
end
