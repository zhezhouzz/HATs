let test (p : Path.t) : int =
  let (x : int) = get p in
  x

let[@assertRty] test ?l:(k = (true : [%v: Path.t])) =
  {
    pre =
      _F
        (Put ((k [@d]), x_1, v, x_1 > 2)
        && _X (_G (not (Put ((k [@d]), x_1, v, true)))));
    res = (v > 2 : [%v: int]);
    post = _G (Any true);
  }
