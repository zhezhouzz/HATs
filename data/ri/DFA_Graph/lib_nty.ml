val addNode : Node.t -> unit
val isNode : Node.t -> bool
val connect : Node.t -> Char.t -> Node.t -> unit
val disconnect : Node.t -> Char.t -> Node.t -> unit
val isConnected : Node.t -> Char.t -> Node.t -> bool
val hasOutEdge : Node.t -> Char.t -> bool
