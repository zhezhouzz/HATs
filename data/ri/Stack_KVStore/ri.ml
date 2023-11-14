let[@pred] rI (p : Cell.t) =
  _G
    (not
       (PutC (x_0, (p [@d]), v, true) && _X (_F (PutC (x_0, (p [@d]), v, true)))))
