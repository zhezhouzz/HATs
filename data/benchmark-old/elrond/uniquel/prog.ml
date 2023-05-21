let rec list_gen (size : int) (x : int) : int ulist =
  let (b : bool) = size == 0 in
  if b then Unil
  else
    let (size2 : int) = size - 1 in
    let (l : int ulist) = list_gen size2 x in
    let (l2 : int ulist) = x +:: l in
    l2
