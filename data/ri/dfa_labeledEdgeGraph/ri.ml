(* let[@pred] rI (s1 : Node.t) (a : Edge.t) (s2 : Node.t) (s3 : Node.t) = *)
(*   implies (is_connect s1 a s2 && is_connect s1 a s3) (_G (Any (s2 == s3))) *)

let[@pred] rI (s1 : Node.t) (a : Edge.t) =
  not
    (_F
       (Connect ((s1 [@d]), (a [@d]), x_2, v, true)
       && _X (_F (Connect ((s1 [@d]), (a [@d]), x_2, v, true)))
       && _X (_G (not (Disconnect ((s1 [@d]), (a [@d]), x_2, v, true))))))
