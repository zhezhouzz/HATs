let rec size_bst_gen (diff : int) (sizebound : int) (lo : int) (hi : int) :
    int tree =
  if diff <= 1 then Leaf
  else if sizebound <= 0 then Leaf
  else if bool_gen () then Leaf
  else
    let (x : int) = int_range lo hi in
    let (lt : int tree) = size_bst_gen (x - lo) (sizebound - 1) lo x in
    let (rt : int tree) = size_bst_gen (hi - x) (sizebound - 1) x hi in
    Node (x, lt, rt)
