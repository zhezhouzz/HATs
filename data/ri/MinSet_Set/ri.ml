(* let[@pred] rI (m : Elem.t) = *)
(*   implies (writtenP m) (minP m) *)
(*   && implies *)
(*        (_G (not (Write (x_0, v, true)))) *)
(*        (_G (not (Insert (x_0, v, true)))) *)

let[@pred] rI (m : Elem.t) =
  _G
    (Write ((m [@d]), v, true) && _X (_G (not (Write (x_0, v, true)))))
    #==> (minP m)
  && implies
       (_G (not (Write (x_0, v, true))))
       (_G (not (Insert (x_0, v, true))))
