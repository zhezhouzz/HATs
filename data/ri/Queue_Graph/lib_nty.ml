val newNode : unit -> Node.t
val putNodeContent : Node.t -> Elem.t -> unit
val hasNodeContent : Node.t -> bool
val getNodeContent : Node.t -> Elem.t
val connect : Node.t -> Node.t -> unit
val hasConnectIn : Node.t -> bool
val hasConnectOut : Node.t -> bool
val isConnected : Node.t -> Node.t -> bool
