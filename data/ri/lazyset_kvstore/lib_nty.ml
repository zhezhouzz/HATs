val put : Key.t -> Elem.t -> unit
val get : Key.t -> Elem.t
val exists : Key.t -> bool
val has_value : Elem.t -> bool
val random_key : unit -> Key.t
