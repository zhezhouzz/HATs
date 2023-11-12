let[@pred] rI (p : Path.t) =
  _G (not (ConnectChild (x_1, x_2, v, not (x_1 == parent x_2))))
  && (_G (Any (is_root p))
     || implies (_F (ConnectChild ((p [@d]), x_2, v, true))) (id_dirP p))

(* let[@pred] rI (p1 : Path.t) (p2 : Path.t) = *)
(*   implies (connected p1 p2) *)
(*     (_G (Any (is_root p1 || p1 == parent p2)) && id_dirP p1) *)
