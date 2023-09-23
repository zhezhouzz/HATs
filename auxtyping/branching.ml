open Language
module P = Rty.P
open Rty
open Sugar

let deseq regex =
  let rec aux res regex =
    match regex with
    | EmptyA -> []
    | AnyA -> [ res ]
    | EpsilonA -> [ res ]
    | StarA _ | EventA _ -> [ res @ [ regex ] ]
    | LorA (t1, t2) -> aux res t1 @ aux res t2
    | SetMinusA (t1, t2) -> aux res t1 @ aux res t2
    | ComplementA _ -> _failatwith __FILE__ __LINE__ "die"
    | LandA (_, _) -> _failatwith __FILE__ __LINE__ "die"
    | SeqA (t1, t2) -> aux (res @ [ t1 ]) t2
  in
  aux [] regex

let branchize_regex regex =
  let last_step preA se =
    match se with
    | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
    | RetEvent pty -> [ (Simp.simp preA, pty) ]
    | EffEvent _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let rec aux preA regex =
    match regex with
    | AnyA -> _failatwith __FILE__ __LINE__ "die"
    | EmptyA -> _failatwith __FILE__ __LINE__ "die"
    | EpsilonA -> _failatwith __FILE__ __LINE__ "die"
    | StarA _ -> _failatwith __FILE__ __LINE__ "die"
    | ComplementA _ -> _failatwith __FILE__ __LINE__ "die"
    | EventA se -> last_step preA se
    | LorA (t1, t2) -> aux preA t1 @ aux preA t2
    | SetMinusA _ -> _failatwith __FILE__ __LINE__ "die"
    | LandA (t1, t2) ->
        let l1 = aux preA t1 in
        let l2 = aux preA t2 in
        let ll =
          List.fold_left
            (fun l (r1, pty1) ->
              List.fold_left
                (fun l (r2, pty2) ->
                  let pty = Fmerge.common_sub_pty (pty1, pty2) in
                  (LandA (r1, r2), pty) :: l)
                l l2)
            [] l1
        in
        ll
    | SeqA (t1, t2) -> aux (SeqA (preA, t1)) t2
  in
  aux EpsilonA regex

(* let branchize = function *)
(*   | Pty pty -> [ (EpsilonA, pty) ] *)
(*   | Regty regex -> branchize_regex EpsilonA regex.Nt.x *)
