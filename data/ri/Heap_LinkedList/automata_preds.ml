let[@pred] headP (value : Elem.t) =
  _F (SetHead ((value [@d]), v, true) && _X (_G (not (SetHead (x_0, v, true)))))

let[@pred] nextP (prev : Elem.t) (value : Elem.t) =
  _F
    (SetNext ((prev [@d]), (value [@d]), v, true)
    && _X
         (_G
            (not
               (DelNext ((prev [@d]), v, true)
               || SetNext ((prev [@d]), x_1, v, true)))))

let[@pred] has_nextP (prev : Elem.t) =
  _F
    (SetNext ((prev [@d]), x_1, v, true)
    && _X (_G (not (DelNext ((prev [@d]), v, true)))))
