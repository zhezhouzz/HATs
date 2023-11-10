let[@pred] memP (k : Elem.t) = _F (Insert ((k [@d]), v, true))

let[@pred] writtenP (idx : Elem.t) =
  _F (Write ((idx [@d]), v, true) && _X (_G (not (Write (x_0, v, true)))))

let[@pred] minP (k : Elem.t) =
  memP k && _G (not (Insert (x_0, v, elem_lt x_0 k)))
