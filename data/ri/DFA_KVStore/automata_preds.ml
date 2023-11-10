let[@pred] storedP (a : Node.t) (c : Char.t) (b : Node.t) =
  _F
    (Put ((a [@d]), (c [@d]), (b [@d]), v, true)
    && _X
         (_G
            (not
               (Put ((a [@d]), (c [@d]), x_2, v, true)
               || Del ((a [@d]), (c [@d]), v, true)))))

let[@pred] existsP (a : Node.t) (c : Char.t) =
  _F
    (Put ((a [@d]), (c [@d]), x_2, v, true)
    && _X (_G (not (Del ((a [@d]), (c [@d]), v, true)))))
