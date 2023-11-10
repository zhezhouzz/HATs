let[@pred] rI (m : Elem.t) =
  implies (writtenP m) (minP m)
  && implies
       (_G (not (Write (x_0, v, true))))
       (_G (not (Put (x_0, x_1, v, true))))
