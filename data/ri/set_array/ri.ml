let[@pred] rI (i : int) (a : Elem.t) =
  _G (not (Init (x_0, v, true) && _X (_F (Init (x_0, v, true)))))
  && _G (not (Write (x_0, v, true) && _X (_F (Init (x_0, v, true)))))
  && _G (not (Init ((i [@d]), v, 0 < i) && _X (_F (Write (x_0, v, i < x_0)))))
  && _G
       (not
          (Update (x_0, (a [@d]), v, true)
          && _X (_F (Update (x_0, (a [@d]), v, true)))))
