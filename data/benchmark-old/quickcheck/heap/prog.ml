let rec heap_gen (size : int) (mx : int) : int heap =
  if size == 0 then Hempty
  else if bool_gen () then Hempty
  else
    let (size1 : int) = size - 1 in
    let (n : int) = int_gen () in
    if n <= mx then
      let (lt : int heap) = heap_gen size1 n in
      let (rt : int heap) = heap_gen size1 n in
      Hnode (n, lt, rt)
    else Hempty
