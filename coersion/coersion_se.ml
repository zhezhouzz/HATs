open Syntax
module Raw = RtyRaw
open Rty
module Q = Coersion_qualifier

let force = function
  | Raw.GuardEvent phi -> GuardEvent (Q.force phi)
  | Raw.EffEvent { op; vs; v; phi } ->
      EffEvent
        {
          op;
          vs = List.map (Coersion_aux.force __FILE__ __LINE__) vs;
          v = (Coersion_aux.force __FILE__ __LINE__) v;
          phi = Q.force phi;
        }

let besome = function
  | GuardEvent phi -> Raw.GuardEvent (Q.besome phi)
  | EffEvent { op; vs; v; phi } ->
      Raw.EffEvent
        {
          op;
          vs = List.map Coersion_aux.besome vs;
          v = Coersion_aux.besome v;
          phi = Q.besome phi;
        }
