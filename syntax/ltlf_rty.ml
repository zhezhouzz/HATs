module F (L : Lit.T) = struct
  open Sexplib.Std
  module R = Rty.F (L)
  module LTLf = R.LTLf
  include LTLf

  (* parsing only *)
  type rty = BaseRty of { cty : cty } | ArrRty of { arr : arr; rethty : hty }
  [@@deriving sexp]

  and arr =
    | NormalArr of string rtyped
    | GhostArr of string Nt.typed
    | ArrArr of rty
  [@@deriving sexp]

  and hty =
    | Rty of rty
    | Htriple of { pre : ltlf; resrty : rty; post : ltlf }
    | Inter of hty * hty
  [@@deriving sexp]

  and 'a rtyped = { rx : 'a; rty : rty } [@@deriving sexp]

  let rec to_hty = function
    | Rty rty -> R.Rty (to_rty rty)
    | Htriple { pre; resrty; post } ->
        R.Htriple
          { pre = to_sfa pre; resrty = to_rty resrty; post = to_sfa post }
    | Inter (hty1, hty2) -> R.Inter (to_hty hty1, to_hty hty2)

  and to_arr = function
    | NormalArr { rx; rty } -> R.(NormalArr { rx; rty = to_rty rty })
    | GhostArr x -> R.GhostArr x
    | ArrArr rty -> ArrArr (to_rty rty)

  and to_rty = function
    | BaseRty { cty } -> R.BaseRty { cty }
    | ArrRty { arr; rethty } ->
        R.ArrRty { arr = to_arr arr; rethty = to_hty rethty }
end
