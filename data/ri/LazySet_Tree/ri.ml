let[@pred] rI =
  _G
    ((not (AddLeft (x_0, x_1, v, elem_lt x_0 x_1 || x_0 == x_1)))
    && not (AddRight (x_0, x_1, v, elem_lt x_1 x_0 || x_0 == x_1)))
