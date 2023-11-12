let[@pred] rI (s1 : Node.t) (s2 : Node.t) (c : Color.t) =
  _G (not (Connect ((s1 [@d]), (s2 [@d]), v, true)))
  || _U
       (not (Connect ((s1 [@d]), (s2 [@d]), v, true)))
       (AddNode ((s1 [@d]), x_1, v, true))
     && _U
          (not (Connect ((s1 [@d]), (s2 [@d]), v, true)))
          (AddNode ((s2 [@d]), x_1, v, true))
     && implies
          (node_has_color s1 c && node_has_color s2 c)
          (_G (not (Connect ((s1 [@d]), (s2 [@d]), v, true))))
