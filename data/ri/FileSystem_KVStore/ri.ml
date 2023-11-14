(* let[@pred] rI (p : Path.t) = *)
(*   _G (Any (is_root p)) *)
(*   || _G (not (Put ((p [@d]), x_1, v, true))) *)
(*   || _U (not (Put ((p [@d]), x_1, v, true))) (mkdirP (parent p)) *)

let[@pred] rI (p : Path.t) =
  _G (Any (is_root p))
  || _G (not (Put ((p [@d]), x_1, v, true)))
  || _U (not (Put (x_0, x_1, v, p == parent x_0 && not (is_del v)))) (mkdirP p)
  || _U (not (Put ((p [@d]), x_1, v, not (is_del v)))) (mkdirP (parent p))

(* let[@pred] rI (p : Path.t) = *)
(*   _G (Any (is_root p)) *)
(*   || implies (aliveP p) (dirP (parent p)) *)
