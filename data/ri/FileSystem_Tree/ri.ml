let[@pred] rI (p : Path.t) =
  _G (not (ConnectChild (x_1, x_2, v, not (x_1 == parent x_2))))
  && (_G (Any (is_root p))
     || implies (_F (ConnectChild ((p [@d]), x_2, v, true))) (id_dirP p))
