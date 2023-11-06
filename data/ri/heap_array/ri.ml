let[@pred] rI (i : int) (a : Elem.t) =
  _G
    (not
       (Update ((i [@d]), (a [@d]), v, true)
       && _X (_F (Update (x_0, x_1, v, i < x_0 && elem_lt x_1 a)))))
