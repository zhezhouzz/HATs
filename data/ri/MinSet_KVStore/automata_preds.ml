let[@pred] storedP (k : Key.t) (value : Elem.t) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : Key.t) = _F (Put ((k [@d]), x_1, v, true))
let[@pred] has_valueP (value : Elem.t) = _F (Put (x_0, (value [@d]), v, true))

let[@pred] writtenP (idx : int) =
  _F (Write ((idx [@d]), v, true) && _X (_G (not (Write (x_0, v, true)))))

let[@pred] minP (value : Elem.t) =
  _F
    (Put (x_0, (value [@d]), v, true)
    && _X (_G (not (Put (x_0, x_1, v, elem_lt x_1 value)))))
