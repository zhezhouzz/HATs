open Language
module P = Rty.P
open Rty
open Sugar

(* NOTE: finalize makes the sigma local type only contains one event *)

let rec finalize regex =
  let rec aux regex =
    match regex with
    | EpsilonA | EventA _ -> regex
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | StarA t -> StarA (aux t)
    | SigmaA { localx; xA; body } ->
        let xA = aux xA in
        let body = aux body in
        finalize_sigmaA (fun se -> SigmaA { localx; xA = EventA se; body }) xA
  in
  aux regex

and finalize_sigmaA k regex =
  let rec aux (k : sevent -> regex) regex =
    match regex with
    | SeqA (t1, t2) -> aux (fun se -> SeqA (t1, k se)) t2
    | SigmaA { localx; xA; body } ->
        aux (fun se -> SigmaA { localx; xA; body = k se }) body
    | StarA _ -> _failatwith __FILE__ __LINE__ "star cannot be the last event"
    | LorA (t1, t2) -> LorA (aux k t1, aux k t2)
    | EpsilonA ->
        _failatwith __FILE__ __LINE__ "epsilon cannot be the last event"
    | LandA (t1, t2) -> LandA (aux k t1, aux k t2)
    | EventA se -> k se
  in
  aux k regex
