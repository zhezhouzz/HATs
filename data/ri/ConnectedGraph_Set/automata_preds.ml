let[@pred] memP (a : Node.t) (b : Node.t) =
  _F (Insert ((a [@d]), (b [@d]), v, true))

let[@pred] mem_fstP (a : Node.t) = _F (Insert ((a [@d]), x_1, v, true))
let[@pred] mem_sndP (b : Node.t) = _F (Insert (x_0, (b [@d]), v, true))
