let[@pred] rI (a : Node.t) (b : Node.t) =
  _G
    (not
       (Insert ((a [@d]), (b [@d]), v, true)
       && _X (_F (Insert ((a [@d]), (b [@d]), v, true)))))
