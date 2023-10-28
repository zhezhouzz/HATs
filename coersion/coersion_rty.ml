open Syntax
module Raw = RtyRaw
open Rty
module Cty = Coersion_cty
module SRL = Coersion_srl

let rec force_arr = function
  | Raw.(NormalArr { rx; rty }) -> NormalArr { rx; rty = force_rty rty }
  | Raw.GhostArr x -> GhostArr x
  | Raw.ArrArr rty -> ArrArr (force_rty rty)

and force_rty = function
  | Raw.BaseRty { cty } -> BaseRty { cty = Cty.force cty }
  | Raw.ArrRty { arr; rethty } ->
      ArrRty { arr = force_arr arr; rethty = force_hty rethty }

and force_hty = function
  | Raw.Rty rty -> Rty (force_rty rty)
  | Raw.Htriple { pre; resrty; post } ->
      Htriple
        {
          pre = SRL.force pre;
          resrty = force_rty resrty;
          post = SRL.force post;
        }
  | Raw.Inter (hty1, hty2) -> Inter (force_hty hty1, force_hty hty2)

let rec besome_arr = function
  | NormalArr { rx; rty } -> Raw.NormalArr { rx; rty = besome_rty rty }
  | GhostArr x -> Raw.GhostArr x
  | ArrArr rty -> Raw.ArrArr (besome_rty rty)

and besome_rty = function
  | BaseRty { cty } -> Raw.BaseRty { cty = Cty.besome cty }
  | ArrRty { arr; rethty } ->
      Raw.ArrRty { arr = besome_arr arr; rethty = besome_hty rethty }

and besome_hty = function
  | Rty rty -> Raw.Rty (besome_rty rty)
  | Htriple { pre; resrty; post } ->
      Raw.Htriple
        {
          pre = SRL.besome pre;
          resrty = besome_rty resrty;
          post = SRL.besome post;
        }
  | Inter (hty1, hty2) -> Raw.Inter (besome_hty hty1, besome_hty hty2)
