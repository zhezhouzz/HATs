(* kvstore *)

let[@pred] memP (k : Elem.t) = _F (Put ((k [@d]), x_1, v, true))
