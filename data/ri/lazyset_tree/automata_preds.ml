(* kvstore *)

let[@pred] memP (k : Elem.t) =
  _F (Init ((k [@d]), v, true) && _X (_F (not (Init (x_0, v, true)))))
