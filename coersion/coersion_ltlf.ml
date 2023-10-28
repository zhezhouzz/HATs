open Syntax
module Raw = RtyRaw.LTLf
open Rty.LTLf
module SE = Coersion_se

let rec force ltlf =
  match ltlf with
  | Raw.EventL sevent -> EventL (SE.force sevent)
  | Raw.NegL a -> NegL (force a)
  | Raw.LorL (a1, a2) -> LorL (force a1, force a2)
  | Raw.LandL (a1, a2) -> LandL (force a1, force a2)
  | Raw.SeqL (a1, a2) -> SeqL (force a1, force a2)
  | Raw.NextL a -> NextL (force a)
  | Raw.UntilL (a1, a2) -> UntilL (force a1, force a2)
  | Raw.FinalL a -> FinalL (force a)
  | Raw.GlobalL a -> GlobalL (force a)
  | Raw.LastL -> LastL

let rec besome ltlf =
  match ltlf with
  | EventL sevent -> Raw.EventL (SE.besome sevent)
  | NegL a -> Raw.NegL (besome a)
  | LorL (a1, a2) -> Raw.LorL (besome a1, besome a2)
  | LandL (a1, a2) -> Raw.LandL (besome a1, besome a2)
  | SeqL (a1, a2) -> Raw.SeqL (besome a1, besome a2)
  | NextL a -> Raw.NextL (besome a)
  | UntilL (a1, a2) -> Raw.UntilL (besome a1, besome a2)
  | FinalL a -> Raw.FinalL (besome a)
  | GlobalL a -> Raw.GlobalL (besome a)
  | LastL -> Raw.LastL

(* let f = if is_even x then if is_odd y then 42 else z else z *)
