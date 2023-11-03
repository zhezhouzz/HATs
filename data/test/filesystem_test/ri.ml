let[@pred] rI (p : Path.t) =
  _G (Any (is_root p))
  || _G (not (Put ((p [@d]), x_1, v, true)))
  || _U (not (Put ((p [@d]), x_1, v, true))) (mkdirP (parent p))
