open Syntax
module Raw = RtyRaw
open Rty
open Coersion_qualifier
(* open Coersion_lit *)

let force_cty Raw.{ v; phi } = { v; phi = force_qualifier phi }
let besome_cty { v; phi } = Raw.{ v; phi = besome_qualifier phi }
let force_arr_kind = function Raw.SigamArr -> SigamArr | Raw.PiArr -> PiArr
let besome_arr_kind = function SigamArr -> Raw.SigamArr | PiArr -> Raw.PiArr

let rec force_pty pty =
  match pty with
  | Raw.BasePty { cty } -> BasePty { cty = force_cty cty }
  | Raw.TuplePty ptys -> TuplePty (List.map force_pty ptys)
  | Raw.ArrPty { arr_kind; rarg; retrty } ->
      let Raw.{ px; pty } = rarg in
      let rarg = px #:: (force_pty pty) in
      ArrPty
        { arr_kind = force_arr_kind arr_kind; rarg; retrty = force_rty retrty }

and force_rty rty =
  match rty with
  | Raw.Pty pty -> Pty (force_pty pty)
  | Raw.Regty { nty; prereg; postreg } ->
      Regty { nty; prereg = force_regex prereg; postreg = force_regex postreg }

and force_sevent = function
  | Raw.GuardEvent phi -> GuardEvent (force_qualifier phi)
  | Raw.RetEvent pty -> RetEvent (force_pty pty)
  | Raw.EffEvent { op; vs; v; phi } ->
      EffEvent { op; vs; v; phi = force_qualifier phi }

and force_regex regex =
  let rec aux regex =
    match regex with
    | Raw.EmptyA -> EmptyA
    | Raw.AnyA -> AnyA
    | Raw.EpsilonA -> EpsilonA
    | Raw.EventA se -> EventA (force_sevent se)
    | Raw.LorA (t1, t2) -> LorA (aux t1, aux t2)
    | Raw.SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
    | Raw.LandA (t1, t2) -> LandA (aux t1, aux t2)
    | Raw.SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | Raw.StarA t -> StarA (aux t)
    | Raw.ComplementA t -> ComplementA (aux t)
  in
  aux regex

let rec besome_pty pty =
  match pty with
  | BasePty { cty } -> Raw.BasePty { cty = besome_cty cty }
  | TuplePty ptys -> Raw.TuplePty (List.map besome_pty ptys)
  | ArrPty { arr_kind; rarg; retrty } ->
      let { px; pty } = rarg in
      let rarg = Raw.(px #:: (besome_pty pty)) in
      Raw.ArrPty
        {
          arr_kind = besome_arr_kind arr_kind;
          rarg;
          retrty = besome_rty retrty;
        }

and besome_rty rty =
  match rty with
  | Pty pty -> Raw.Pty (besome_pty pty)
  | Regty { nty; prereg; postreg } ->
      Raw.Regty
        { nty; prereg = besome_regex prereg; postreg = besome_regex postreg }

and besome_sevent = function
  | GuardEvent phi -> Raw.GuardEvent (besome_qualifier phi)
  | RetEvent pty -> Raw.RetEvent (besome_pty pty)
  | EffEvent { op; vs; v; phi } ->
      Raw.EffEvent { op; vs; v; phi = besome_qualifier phi }

and besome_regex regex =
  let rec aux regex =
    match regex with
    | EmptyA -> Raw.EmptyA
    | AnyA -> Raw.AnyA
    | EpsilonA -> Raw.EpsilonA
    | EventA se -> Raw.EventA (besome_sevent se)
    | LorA (t1, t2) -> Raw.LorA (aux t1, aux t2)
    | SetMinusA (t1, t2) -> Raw.SetMinusA (aux t1, aux t2)
    | LandA (t1, t2) -> Raw.LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> Raw.SeqA (aux t1, aux t2)
    | StarA t -> Raw.StarA (aux t)
    | ComplementA t -> Raw.ComplementA (aux t)
  in
  aux regex
