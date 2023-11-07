(* multi-tree *)

let[@pred] storedP (k : Path.t) (value : Bytes.t) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] id_dirP (k : Path.t) =
  _F
    (Put ((k [@d]), x_1, v, is_dir x_1)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] connectedP (k1 : Path.t) (k2 : Path.t) =
  _F (Connect_child ((k1 [@d]), (k2 [@d]), v, true))

let[@pred] memP (k : Path.t) =
  _F (Connect_child (x_0, (k [@d]), v, true)) || _F (Init ((k [@d]), v, true))
