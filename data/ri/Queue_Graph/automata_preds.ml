let[@pred] is_connected (s1 : Node.t) (s2 : Node.t) =
  _F (Connect ((s1 [@d]), (s2 [@d]), v, true))

let[@pred] has_connect_in (s2 : Node.t) = _F (Connect (x_0, (s2 [@d]), v, true))

let[@pred] has_connect_out (s1 : Node.t) =
  _F (Connect ((s1 [@d]), x_1, v, true))

let[@pred] is_node (s : Node.t) = _F (PutNodeContent ((s [@d]), x_1, v, true))

let[@pred] storeP (c : Node.t) (a : Elem.t) =
  _F
    (PutNodeContent ((c [@d]), (a [@d]), v, true)
    && _X (_G (not (PutNodeContent ((c [@d]), x_1, v, true)))))
