let[@pred] rI (s1 : Node.t) (a : Edge.t) =
  not
    (_F
       (Connect ((s1 [@d]), (a [@d]), x_2, v, true)
       && _X
            (_U
               (not (Disconnect ((s1 [@d]), (a [@d]), x_2, v, true)))
               (Connect ((s1 [@d]), (a [@d]), x_2, v, true)))))
