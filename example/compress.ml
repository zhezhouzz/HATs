let rec gen1 (n : int) =
  if n == 0 then ()
  else
    let key = RandomKey () in
    let value = RandomValue () in
    Write (key, value);
    gen1 (n - 1)

(* maybe get some keys are compressed *)

let rec gen2 (n : int) =
  if n == 0 then ()
  else
    let key = RandomKey () in
    let value = RandomValue () in
    Write (key, value);
    if IsCompress () then (
      Delete key;
      gen2 n)
    else gen2 (n - 1)

(* maybe pollute the previous keys  *)

let rec gen3 (n : int) =
  if n == 0 then ()
  else
    let key = RandomKey () in
    let value = RandomValue () in
    Write (key, value);
    let m = delete_compressed () in
    gen (n - 1 + m)

(* iterate the keys in the database!  *)

let rec gen4 (n : int) =
  if n == 0 then ()
  else
    let key = RandomKey () in
    let key' = set_prefix n key in
    let value = RandomValue () in
    Write (key', value);
    IsCompress key';
    gen4 (n - 1)

(* n:{v:int | v >= 0} -> *)
(*     [unit | (. - <Write x v | prefix x >= n>)* => *)
(*             <Write x v | prefix x == n><IsCompress x v | prefix x == n /\ v = false> ] *)

(* IsCompress: k:int -> [int | (. - <Write x v | prefix x != k)* => {v:bool| v = false} ] *)

(* IsCompress: k:int -> [int | .* => {v:bool| v = false \/ v = true} ] *)

let rec bst_gen (l : int list) : int tree =
  match l with [] -> Leaf | h :: t -> insert t (bst_gen t)
