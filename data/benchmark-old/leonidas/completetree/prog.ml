let rec complete_tree_gen (size : int) : int ctree =
  let (b : bool) = size == 0 in
  if b then Cleaf
  else
    let (size1 : int) = size - 1 in
    let (lt : int ctree) = complete_tree_gen size1 in
    let (rt : int ctree) = complete_tree_gen size1 in
    let (n : int) = int_gen () in
    Cnode (n, lt, rt)
