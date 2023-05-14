open Syntax
module Raw = RtyRaw
open Rty

let force_ou = function Raw.Over -> Over | Raw.Under -> Under
let besome_ou = function Over -> Raw.Over | Under -> Raw.Under

open Coersion_qualifier
(* open Coersion_lit *)

let force_cty Raw.{ v; phi } = { v; phi = force_qualifier phi }
let besome_cty { v; phi } = Raw.{ v; phi = besome_qualifier phi }

let rec force_pty pty =
  match pty with
  | Raw.BasePty { ou; cty } -> BasePty { ou = force_ou ou; cty = force_cty cty }
  | Raw.TuplePty ptys -> TuplePty (List.map force_pty ptys)
  | Raw.ArrPty { rarg; retrty } ->
      let Raw.{ px; pty } = rarg in
      let rarg = px #:: (force_pty pty) in
      ArrPty { rarg; retrty = force_rty retrty }

and force_rty rty =
  match rty with
  | Raw.Pty pty -> Pty (force_pty pty)
  | Raw.Regty regex -> Regty Nt.(force_regex #-> regex)

and force_sevent = function
  | Raw.GuardEvent phi -> GuardEvent (force_qualifier phi)
  | Raw.RetEvent pty -> RetEvent (force_pty pty)
  | Raw.EffEvent { op; vs; phi } ->
      EffEvent { op; vs; phi = force_qualifier phi }

and force_regex regex =
  let rec aux regex =
    match regex with
    | Raw.EpsilonA -> EpsilonA
    | Raw.EventA se -> EventA (force_sevent se)
    | Raw.LorA (t1, t2) -> LorA (aux t1, aux t2)
    | Raw.LandA (t1, t2) -> LandA (aux t1, aux t2)
    | Raw.SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | Raw.StarA t -> StarA (aux t)
    | Raw.SigmaA { localx; xA; body } ->
        SigmaA { localx; xA = aux xA; body = aux body }
  in
  aux regex

let rec besome_pty pty =
  match pty with
  | BasePty { ou; cty } ->
      Raw.BasePty { ou = besome_ou ou; cty = besome_cty cty }
  | TuplePty ptys -> Raw.TuplePty (List.map besome_pty ptys)
  | ArrPty { rarg; retrty } ->
      let { px; pty } = rarg in
      let rarg = Raw.(px #:: (besome_pty pty)) in
      Raw.ArrPty { rarg; retrty = besome_rty retrty }

and besome_rty rty =
  match rty with
  | Pty pty -> Raw.Pty (besome_pty pty)
  | Regty regex -> Raw.Regty Nt.(besome_regex #-> regex)

and besome_sevent = function
  | GuardEvent phi -> Raw.GuardEvent (besome_qualifier phi)
  | RetEvent pty -> Raw.RetEvent (besome_pty pty)
  | EffEvent { op; vs; phi } ->
      Raw.EffEvent { op; vs; phi = besome_qualifier phi }

and besome_regex regex =
  let rec aux regex =
    match regex with
    | EpsilonA -> Raw.EpsilonA
    | EventA se -> Raw.EventA (besome_sevent se)
    | LorA (t1, t2) -> Raw.LorA (aux t1, aux t2)
    | LandA (t1, t2) -> Raw.LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> Raw.SeqA (aux t1, aux t2)
    | StarA t -> Raw.StarA (aux t)
    | SigmaA { localx; xA; body } ->
        Raw.SigmaA { localx; xA = aux xA; body = aux body }
  in
  aux regex
