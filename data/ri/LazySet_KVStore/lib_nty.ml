val put : Key.t -> Elem.t -> unit
val get : Key.t -> Elem.t
val exists : Key.t -> bool
val hasValue : Elem.t -> bool
val randomKey : unit -> Key.t
