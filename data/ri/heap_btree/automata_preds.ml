let[@pred] rootP (k : Elem.t) = _F (PutRoot ((k [@d]), v, true))
let[@pred] has_rootP (k : Elem.t) = _F (PutRoot ((k [@d]), v, true))
let[@pred] has_leftP (k : Elem.t) = _F (AddLeft ((k [@d]), x_1, v, true))
let[@pred] has_rightP (k : Elem.t) = _F (AddRight ((k [@d]), x_1, v, true))

let[@pred] memP (k : Elem.t) =
  _F
    (PutRoot ((k [@d]), v, true)
    || AddLeft (x_0, (k [@d]), v, true)
    || AddRight (x_0, (k [@d]), v, true))
