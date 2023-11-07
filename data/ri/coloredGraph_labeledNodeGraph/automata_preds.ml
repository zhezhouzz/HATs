let[@pred] is_connected (s1 : Node.t) (s2 : Node.t) =
  _F
    (Connect ((s1 [@d]), (s2 [@d]), v, true)
    && _X (_G (not (Disconnect ((s1 [@d]), (s2 [@d]), v, true)))))

let[@pred] is_node (s : Node.t) = _F (AddNode ((s [@d]), x_1, v, true))

let[@pred] node_has_color (s : Node.t) (c : Color.t) =
  _F (AddNode ((s [@d]), (c [@d]), v, true))
