val ( && ) : bool -> bool -> bool

(* == is poly *)
val ( == ) : int -> int -> bool
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

(* path *)
val parent : Path.t -> Path.t
val is_root : Path.t -> bool

(* bytes *)
val is_del : Bytes.t -> bool
val is_dir : Bytes.t -> bool
val add_child : Bytes.t -> Path.t -> Bytes.t
val del_child : Bytes.t -> Path.t -> Bytes.t
val is_child : Bytes.t -> Path.t -> bool
val has_child : Bytes.t -> bool

(* elem *)
val elem_lt : Elem.t -> Elem.t -> bool
val elem_eq : Elem.t -> Elem.t -> bool

(* color *)
val color_eq : Color.t -> Color.t -> bool

(* node *)
val node_eq : Node.t -> Node.t -> bool

(* cell *)
val cell_eq : Cell.t -> Cell.t -> bool

(* eff operator **)

(* set *)
val set_insert : int -> unit
val set_mem : int -> bool
