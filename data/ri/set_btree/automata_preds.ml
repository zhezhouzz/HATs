(* let[@pred] rootP (k : Elem.t) = *)
(*   _F (Put_root ((k [@d]), v, true) && _X (_G (not (Put_root (x_0, v, true))))) *)

let[@pred] rootP (k : Elem.t) = _F (Put_root ((k [@d]), v, true))
let[@pred] has_rootP (k : Elem.t) = _F (Put_root ((k [@d]), v, true))
let[@pred] has_leftP (k : Elem.t) = _F (Add_left ((k [@d]), x_1, v, true))
let[@pred] has_rightP (k : Elem.t) = _F (Add_right ((k [@d]), x_1, v, true))

let[@pred] memP (k : Elem.t) =
  _F
    (Put_root ((k [@d]), v, true)
    || Add_left (x_0, (k [@d]), v, true)
    || Add_right (x_0, (k [@d]), v, true))
