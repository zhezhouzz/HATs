module SyntaxF (A : Sfa.SFA) (L : Lit.T) = struct
  open Sexplib.Std
  module Cty = Cty.F (L)
  include Cty

  type rty = BaseRty of { cty : cty } | ArrRty of { arr : arr; rethty : hty }
  [@@deriving sexp]

  and arr =
    | NormalArr of string rtyped
    | GhostArr of string Nt.typed
    | ArrArr of rty
  [@@deriving sexp]

  and hty =
    | Rty of rty
    | Htriple of { pre : A.sfa; resrty : rty; post : A.sfa }
    | Inter of hty * hty
  [@@deriving sexp]

  and 'a rtyped = { rx : 'a; rty : rty } [@@deriving sexp]

  type 'a htyped = { hx : 'a; hty : hty } [@@deriving sexp]

  (* erase *)
  open Sugar

  let rec erase_rty rty =
    let open Nt in
    match rty with
    | BaseRty { cty; _ } -> Cty.erase cty
    | ArrRty { arr; rethty } -> mk_arr (erase_arr arr) (erase_hty rethty)

  and erase_arr = function
    | NormalArr { rty; _ } -> erase_rty rty
    | GhostArr Nt.{ ty; _ } -> ty
    | ArrArr rty -> erase_rty rty

  and erase_hty rty =
    (* let open Nt in *)
    match rty with
    | Rty rty -> erase_rty rty
    | Htriple { resrty; _ } -> erase_rty resrty
    | Inter (hty1, hty2) ->
        let ty1 = erase_hty hty1 in
        let ty2 = erase_hty hty2 in
        let _ = _assert __FILE__ __LINE__ "eq" (Nt.eq ty1 ty2) in
        ty1

  let rtyped_erase { rx; rty } = Nt.{ x = rx; ty = erase_rty rty }

  let rty_to_cty rty =
    match rty with
    | BaseRty { cty } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let htyped_force_to_rtyped file line { hx; hty } =
    match hty with
    | Rty rty -> { rx = hx; rty }
    | _ -> _failatwith file line "die"
end
