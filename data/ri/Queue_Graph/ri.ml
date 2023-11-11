let[@pred] rI (n : Node.t) =
  _G (not (Connect (x_0, x_1, v, x_0 == x_1)))
  && _G
       (not
          (Connect ((n [@d]), x_1, v, true)
          && _X (_F (Connect ((n [@d]), x_1, v, true)))))
  && _G
       (not
          (Connect (x_0, (n [@d]), v, true)
          && _X (_F (Connect (x_0, (n [@d]), v, true)))))
