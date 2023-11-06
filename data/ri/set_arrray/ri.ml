let[@pred] rI (a : Elem.t) =
  (_G (not (Init (x_0, v, true)))
  || _F (Init (x_0, v, true) && _X (Write (x_0, v, x_0 == 0))))
  && _G
       (not
          (Update (x_0, (a [@d]), v, true)
          && _X (_F (Update (x_0, (a [@d]), v, true)))))
