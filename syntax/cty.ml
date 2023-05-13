module F (L : Lit.T) = struct
  open Sexplib.Std
  module Nt = Lit.Ty
  module P = Qualifier.F (L)
  include P

  type cty = { v : string Nt.typed; phi : prop } [@@deriving sexp]
  type 'a ctyped = { cx : 'a; cty : cty }

  (* open Sugar *)

  let v_name = "v"
  let ( #::: ) cx cty = { cx; cty }
  let ( #---> ) f { cx; cty } = { cx = f cx; cty }

  let cty_typed_to_prop { cx; cty = { v; phi } } =
    let Nt.{ x; ty } = v in
    (Nt.{ x = cx; ty }, P.subst_prop_id (x, cx) phi)

  (* subst *)
  let subst_cty (y, replacable) { v; phi } =
    if String.equal y v.Nt.x then { v; phi }
    else { v; phi = subst_prop (y, replacable) phi }

  let subst_cty_id (y, z) cty =
    let z = AVar z in
    subst_cty (y, z) cty

  (* fv *)
  let fv_cty { v; phi } =
    List.filter (fun x -> String.equal x v.x) @@ fv_prop phi

  (* erase *)

  (* open Zzdatatype.Datatype *)

  let erase_cty { v; _ } = v.Nt.ty

  (* normalize name *)

  let normalize_name_cty { v; phi } =
    let phi = P.(subst_prop_id (v.x, v_name) phi) in
    let v = Nt.{ x = v_name; ty = v.ty } in
    { v; phi }

  (* mk bot/top *)

  let mk_unit_cty_from_prop phi = Nt.{ v = v_name #: Ty_unit; phi }
  let mk_bot_cty nt = Nt.{ v = v_name #: nt; phi = mk_false }
  let mk_top_cty nt = Nt.{ v = v_name #: nt; phi = mk_true }
end
