let[@pred] rI (p1 : Path.t) (p2 : Path.t) =
  implies (connectedP p1 p2)
    (_G (Any (is_root p1 || p1 == parent p2)) && id_dirP p1)
