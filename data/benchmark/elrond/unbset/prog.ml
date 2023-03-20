let rec unbset_gen (diff : int) (sizebound : int) (lo : int) (hi : int) :
    int unbset =
  if diff <= 1 then Usleaf
  else if sizebound <= 0 then Usleaf
  else if bool_gen () then Usleaf
  else
    let (x : int) = int_range lo hi in
    let (lt : int unbset) = unbset_gen (x - lo) (x - lo) lo x in
    let (rt : int unbset) = unbset_gen (hi - x) (hi - x) x hi in
    Usnode (x, lt, rt)
