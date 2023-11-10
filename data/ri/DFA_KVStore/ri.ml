let[@pred] rI (a : Node.t) (c : Char.t) =
  _G
    (not
       (Put ((a [@d]), (c [@d]), x_2, v, true)
       && _G (not (Del ((a [@d]), (c [@d]), v, true)))
       && _X (_F (Put ((a [@d]), (c [@d]), x_2, v, true)))))
