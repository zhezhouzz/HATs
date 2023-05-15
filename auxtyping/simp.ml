open Language
module P = Rty.P
open Rty
(* open Sugar *)

let simp regex =
  let rec aux regex =
    match regex with
    | EpsilonA | EventA _ -> regex
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> (
        match (aux t1, aux t2) with
        | EpsilonA, regex2 -> regex2
        | regex1, EpsilonA -> regex1
        | EventA (GuardEvent phi1), EventA (GuardEvent phi2) ->
            EventA (GuardEvent (P.smart_and [ phi1; phi2 ]))
        | EventA (GuardEvent phi1), SeqA (EventA (GuardEvent phi2), r) ->
            aux (SeqA (EventA (GuardEvent (P.smart_and [ phi1; phi2 ])), r))
        | regex1, regex2 -> SeqA (regex1, regex2))
    | StarA t -> StarA (aux t)
    | SigmaA { localx; xA; body } ->
        let xA = aux xA in
        let body = aux body in
        SigmaA { localx; xA; body }
  in
  aux regex
