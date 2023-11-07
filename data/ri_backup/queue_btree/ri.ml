let[@pred] rI =
  _G
    ((not (Add_left (x_0, x_1, v, elem_lt x_0 x_1 || x_0 == x_1)))
    || not (Add_right (x_0, x_1, v, elem_lt x_1 x_0 || x_0 == x_1)))
