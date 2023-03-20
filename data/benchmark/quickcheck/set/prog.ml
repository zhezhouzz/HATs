let rec set_gen (diff : int) (lo : int) (hi : int) : int set =
  if hi <= 1 + lo then Sempty
  else if bool_gen () then Sempty
  else
    let (x : int) = int_range lo hi in
    let (diff1 : int) = x - lo in
    let (lt : int set) = set_gen diff1 lo x in
    let (diff2 : int) = hi - x in
    let (rt : int set) = set_gen diff2 x hi in
    Snode (x, lt, rt)
