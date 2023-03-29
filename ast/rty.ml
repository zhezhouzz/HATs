module F (Ty : Typed.T) = struct
  module Nt = Normalty.Ntyped
  module P = Qualifier.F (Ty)

  type basety = { h : string Nt.typed; v : string Nt.typed; phi : P.t }
  type ou = Over | Under
  type dep = Sigma | Pi

  type t =
    | BaseRty of { ou : ou; basety : basety }
    | DepRty of {
        dep : dep;
        label : Leff.t;
        rarg : string option typed;
        retrty : t;
      }

  and 'a typed = { x : 'a; ty : t }

  let ( #: ) x ty = { x; ty }

  let subst_id_basety (y, z) { h; v; phi } =
    if String.equal y h.Nt.x || String.equal y v.Nt.x then { h; v; phi }
    else { h; v; phi = P.subst_id (y, z) phi }

  let subst_id (y, z) rty =
    let rec aux rty =
      match rty with
      | BaseRty { basety; ou } ->
          BaseRty { basety = subst_id_basety (y, z) basety; ou }
      | DepRty { dep; label; rarg; retrty } -> (
          let rarg = rarg.x #: (aux rarg.ty) in
          match rarg.x with
          | Some x when String.equal y x -> DepRty { dep; label; rarg; retrty }
          | _ -> DepRty { dep; label; rarg; retrty = aux retrty })
    in
    aux rty

  let erase_basety { v; _ } = v.Nt.ty

  let rec erase rty =
    let open Nt in
    match rty with
    | BaseRty { basety; _ } -> erase_basety basety
    | DepRty { dep; label; rarg; retrty } -> (
        let t1 = erase rarg.ty in
        let t2 = erase retrty in
        match dep with
        | Sigma -> Ty_tuple [ t1; t2 ]
        | Pi -> Ty_arrow (label, t1, t2))

  open Sugar

  let default_ty =
    BaseRty
      {
        ou = Over;
        basety = Nt.{ h = "h" #: Ty_unit; v = "v" #: Ty_unit; phi = P.mk_true };
      }

  let mk_noty x = { x; ty = default_ty }
  let xmap f { x; ty } = { x = f x; ty }
  let is_basic_tp = function BaseRty _ -> true | _ -> false
  let is_dt _ = _failatwith __FILE__ __LINE__ "never happen"

  (* TODO: imp eq *)
  let eq _ _ = false
  let destruct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let construct_normal_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify _ _ = _failatwith __FILE__ __LINE__ "unimp"

  let is_eff_arr = function
    | DepRty { dep = Pi; label = Some Leff.EffArr; _ } -> true
    | _ -> false

  let to_smttyped _ = _failatwith __FILE__ __LINE__ "unimp"
  let typed_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_typed _ = _failatwith __FILE__ __LINE__ "unimp"
  let is_hd_arr _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify_ _ = _failatwith __FILE__ __LINE__ "unimp"

  let destruct_arr_one rty =
    match rty with
    | DepRty { dep = Pi; label; rarg; retrty } -> (rarg, label, retrty)
    | _ -> _failatwith __FILE__ __LINE__ ""

  let get_argty rty =
    let rarg, _, _ = destruct_arr_one rty in
    rarg.ty

  let get_retty rty =
    let _, _, retrty = destruct_arr_one rty in
    retrty

  let snd_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let fst_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let bool_ty = default_ty
  let mk_tuple _ = _failatwith __FILE__ __LINE__ "unimp"

  let mk_arr ?(lb = None) _ =
    let _ = Leff.sexp_of_t lb in
    _failatwith __FILE__ __LINE__ "unimp"

  let int_ty = default_ty
  let unit_ty = default_ty
  let to_smtty _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_t _ = _failatwith __FILE__ __LINE__ "unimp"
  let t_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
end
