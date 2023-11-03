(* kvstore *)

let[@pred] storedP (k : Path.t) (value : Bytes.t) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : Path.t) = _F (Put ((k [@d]), x_1, v, true))

let[@pred] mkdirP (p : Path.t) =
  Put ((p [@d]), x_1, v, is_dir x_1)
  && _X (_G (not (Put ((p [@d]), x_1, v, is_deleted x_1))))

(* multi-tree *)

let[@pred] mtree_storedP (k : Path.t) (value : Bytes.t) =
  _F
    (Mtree_put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Mtree_put ((k [@d]), x_1, v, true)))))

let[@pred] mtree_id_dirP (k : Path.t) =
  _F
    (Mtree_put ((k [@d]), x_1, v, is_dir x_1)
    && _X (_G (not (Mtree_put ((k [@d]), x_1, v, true)))))

let[@pred] mtree_connected (k1 : Path.t) (k2 : Path.t) =
  _F (Mtree_add_child ((k1 [@d]), (k2 [@d]), v, true))

let[@pred] mtree_memP (k : Path.t) =
  _F (Mtree_add_child (x_0, (k [@d]), v, true))
  || _F (Mtree_init ((k [@d]), v, true))
