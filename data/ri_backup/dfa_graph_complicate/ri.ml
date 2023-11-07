let[@pred] rI (s1 : Node.t) (a : Edge.t) (s2 : Node.t) =
  implies (is_trans s1 a s2)
    (_G (not (Connect ((s1 [@d]), (a [@d]), x_2, v, not (x_2 == s2)))))

(* let[@pred] rI (s1 : Node.t) (a : Edge.t) = *)
(*   not *)
(*     (_F *)
(*        (Connect ((s1 [@d]), (a [@d]), x_2, v, true) *)
(*        && _X (_F (Connect ((s1 [@d]), (a [@d]), x_2, v, true))) *)
(*        && _X (_G (not (Disconnect ((s1 [@d]), (a [@d]), x_2, v, true)))))) *)
