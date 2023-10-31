val ( && ) : bool -> bool -> bool
val ( == ) : int -> int -> bool

(* val eqn : nat -> nat -> bool *)
val ( != ) : int -> int -> bool
val ( < ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( mod ) : int -> int -> int
val ( * ) : int -> int -> int
val ( / ) : int -> int -> int
val not : bool -> bool
val parent : int -> int
val is_root : int -> bool
val is_deleted : int -> bool
val is_dir : int -> bool
val add_child : int -> int -> int
val del_child : int -> int -> int

(* eff operator **)

val put : int -> int -> unit
val get : int -> int
val exists : int -> bool
val setinsert : int -> unit
val setmem : int -> bool
