let[@pred] storedCP (k : Node.t) (c : Color.t) =
  _F
    (PutC ((k [@d]), (c [@d]), v, true)
    && _X (_G (not (PutC ((k [@d]), x_1, v, true)))))

let[@pred] existsCP (k : Node.t) = _F (PutC ((k [@d]), x_1, v, true))

let[@pred] existsEP (n1 : Node.t) (n2 : Node.t) =
  _F (PutE ((n1 [@d]), (n2 [@d]), v, true))
