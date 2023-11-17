let[@pred] rI (p : Path.t) =
  _G (Any (is_root p)) || implies (aliveP p) (dirP (parent p))
