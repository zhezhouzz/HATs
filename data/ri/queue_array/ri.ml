let[@pred] rI (n : int) =
  _G (not (Init (x_0, v, true) && _X (_F (Init (x_0, v, true)))))
  && _G (not (Write (x_0, v, true) && _X (_F (Init (x_0, v, true)))))
  && _G (not (Init ((n [@d]), v, 0 < n) && _X (_F (Write (x_0, v, n < x_0)))))
