open Sugar
open Zzdatatype.Datatype
open QCheck

type 'a t = Random.State.t -> 'a

let nat_gen : int t = Gen.small_nat

let list_gen_wrong : int list t =
 fun (r : Random.State.t) ->
  let len = nat_gen r in
  let elem = nat_gen r in
  let rec aux (n : int) : int list =
    if n == 0 then [] else elem :: aux (n - 1)
  in
  aux len

let list_gen_correct : int list t =
 fun (r : Random.State.t) ->
  let len = nat_gen r in
  let rec aux (n : int) : int list =
    if n == 0 then [] else nat_gen r :: aux (n - 1)
  in
  aux len

let rec bst_gen (low : int) (high : int) : int Tree.t t =
 fun r ->
  if high <= low + 1 then Tree.Leaf
  else
    Gen.frequencyl
      [
        (* (1, Tree.Leaf); *)
        ( 1,
          let x = Gen.int_range (low + 1) (high - 1) r in
          let lt = (bst_gen low x) r in
          let rt = (bst_gen x high) r in
          Tree.Node (x, lt, rt) );
      ]
      r

let rec is_bst (low : int) (high : int) = function
  | Tree.Leaf -> true
  | Tree.Node (x, lt, rt) ->
      if low < x && x < high then is_bst low x lt && is_bst x high rt else false

let sized_gen (low : int) (high : int) : int Tree.t t =
  Gen.(
    sized_size (int_range 0 (high - low))
    @@ fix (fun self n ->
           match n with
           | 0 -> pure Tree.Leaf
           | n ->
               frequency
                 [
                   (1, pure Tree.Leaf);
                   ( 2,
                     map3
                       (fun x lt rt -> Tree.Node (x, lt, rt))
                       (int_range low high)
                       (self (n - 1))
                       (self (n - 1)) );
                 ]))

(* let test (num : int) = *)
(*   let ls1 = Gen.generate ~n:num (bst_gen 0 4) in *)
(*   let ls1 = List.filter (is_bst 0 4) ls1 in *)
(*   let ls1 = List.slow_rm_dup (Tree.eq ( = )) ls1 in *)
(*   let () = *)
(*     List.iter (fun t -> Printf.printf "%s\n" @@ Tree.layout string_of_int t) ls1 *)
(*   in *)
(*   let () = Printf.printf "bst: %i\n" @@ List.length ls1 in *)
(*   let ls1 = Gen.generate ~n:(num * 1000) (sized_gen 0 4) in *)
(*   let ls1 = List.filter (is_bst 0 4) ls1 in *)
(*   let ls1 = List.slow_rm_dup (Tree.eq ( = )) ls1 in *)
(*   let () = *)
(*     List.iter (fun t -> Printf.printf "%s\n" @@ Tree.layout string_of_int t) ls1 *)
(*   in *)
(*   let () = Printf.printf "bst: %i\n" @@ List.length ls1 in *)
(*   () *)
