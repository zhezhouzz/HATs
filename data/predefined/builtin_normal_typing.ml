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
val parent : Path.t -> Path.t
val is_root : Path.t -> bool
val is_deleted : Bytes.t -> bool
val is_dir : Bytes.t -> bool
val add_child : Bytes.t -> Path.t -> Bytes.t
val del_child : Bytes.t -> Path.t -> Bytes.t

(* eff operator **)

val put : Path.t -> Bytes.t -> unit
val get : Path.t -> Bytes.t
val exists : Path.t -> bool
val setinsert : int -> unit
val setmem : int -> bool
