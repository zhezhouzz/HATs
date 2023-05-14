open Language
module P = Rty.P
open Rty
open Sugar

(* NOTE: <Get 3> ==> Sigma x:<Get 3>. Ret [v:int | v == x] *)

let fresh_local_x ty = Nt.{ x = Rename.unique "localx"; ty }

let retilize nty regex =
  let last_step se =
    match se with
    | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
    | RetEvent _ -> EventA se
    | EffEvent _ ->
        let localx = fresh_local_x nty in
        let pty = mk_pty_var_eq_var localx in
        SigmaA { localx; xA = EventA se; body = EventA (RetEvent pty) }
  in
  let rec aux regex =
    match regex with
    | EpsilonA -> _failatwith __FILE__ __LINE__ "die"
    | EventA se -> last_step se
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> SeqA (t1, aux t2)
    | SigmaA { localx; xA; body } -> SigmaA { localx; xA; body = aux body }
    | StarA _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux regex
