(* multi-tree *)
val init : Path.t -> unit
val connect_child : Path.t -> Path.t -> unit
val mem : Path.t -> bool
val put : Path.t -> Bytes.t -> unit
val get : Path.t -> Bytes.t
