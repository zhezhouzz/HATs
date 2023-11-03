val ( && ) : bool -> bool -> bool

(* == is poly *)
(* val ( == ) : int -> int -> bool *)
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

(* set *)
val set_insert : int -> unit
val set_mem : int -> bool

(* val mtree_get_parent : Path.t -> Path.t *)
(* val mtree_add_child : Path.t -> Path.t -> Bytes.t -> unit *)
(* val mtree_del_child : Path.t -> Path.t -> unit *)
