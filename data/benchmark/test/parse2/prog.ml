let rty1 = ()
let rty2 = ()

(* let hd = *)
(*   { *)
(*     retc = (fun (v : int) -> v); *)
(*     put = (fun (k : unit -> int) (_ : int) -> k ()); *)
(*     get = (fun (k : int -> int) (i : int) -> k i); *)
(*   } *)

let f (x : eff:int -> int) = x
let g (x : hd:int -> int) = x
let k (x : int -> int) = x

type t = A of t | B of bool
type 'a list = Nil | Cons of 'a * 'a list
type 'a t = A of 'a t | B of 'a * bool

type 'a effect =
  | Put of int * unit effect
  | Get of int * int effect
  | Dummy of ((int * int) * int) * unit effect

val ( + ) : int -> int -> int

let x = 1 + 2
let x = Err
let x = []
let x = 1 :: [ 2 ]
let x = perform (Dummy ((2, 3), 2))

(* let x = *)
(*   match_with 1 *)
(*     { *)
(*       retc = (fun (v : int) -> v); *)
(*       put = (fun (k : unit -> int) (_ : int) -> k ()); *)
(*       get = (fun (k : int -> int) (i : int) -> k i); *)
(*     } *)
