let rec leftisthp_gen (size : int) : int leftisthp =
  let (b : bool) = size == 0 in
  if b then Lhpleaf
  else
    let (size1 : int) = size - 1 in
    let (lt : int leftisthp) = leftisthp_gen size1 in
    let (size2 : int) = int_range_inc 0 size1 in
    let (rt : int leftisthp) = leftisthp_gen size2 in
    let (n : int) = int_gen () in
    Lhpnode (n, lt, rt, size2)
