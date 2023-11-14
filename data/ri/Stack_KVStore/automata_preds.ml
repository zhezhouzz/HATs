let[@pred] storedCP (k : Cell.t) (c : Cell.t) =
  _F
    (PutC ((k [@d]), (c [@d]), v, true)
    && _X (_G (not (PutC ((k [@d]), x_1, v, true)))))

let[@pred] storedEP (k : Cell.t) (a : Elem.t) =
  _F
    (PutE ((k [@d]), (a [@d]), v, true)
    && _X (_G (not (PutE ((k [@d]), x_1, v, true)))))

let[@pred] existsCP (k : Cell.t) = _F (PutC ((k [@d]), x_1, v, true))
let[@pred] existsValCP (k : Cell.t) = _F (PutC (x_0, (k [@d]), v, true))
let[@pred] existsEP (k : Cell.t) = _F (PutE ((k [@d]), x_1, v, true))
