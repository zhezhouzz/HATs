let[@pred] storedP (k : Key.t) (value : Elem.t) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : Key.t) = _F (Put ((k [@d]), x_1, v, true))
let[@pred] has_valueP (value : Elem.t) = _F (Put (x_0, (value [@d]), v, true))
