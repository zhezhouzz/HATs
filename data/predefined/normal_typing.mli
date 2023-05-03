type 'a list = Nil | Cons of 'a * 'a list
type 'a effect = Put of int * unit effect | Get of int * int effect

val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int

(* test *)
val tr_len : tr -> int
