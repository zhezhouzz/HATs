let[@pred] is_trans (s1 : Node.t) (a : Edge.t) (s2 : Node.t) =
  _F
    (Connect ((s1 [@d]), (a [@d]), (s2 [@d]), v, true)
    && _X (_G (not (Disconnect ((s1 [@d]), (a [@d]), (s2 [@d]), v, true)))))

let[@pred] is_node (s : Node.t) = _F (AddNode ((s [@d]), v, true))

let[@pred] has_out_edge (s : Node.t) (c : Char.t) =
  _F
    (Connect ((s1 [@d]), (c [@d]), x_2, v, true)
    && _X (_G (not (Disconnect ((s1 [@d]), (c [@d]), x_2, v, true)))))
