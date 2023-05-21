let rec sized_list_gen (size : int) : int list =
  let (b : bool) = size == 0 in
  if b then []
  else
    let (b1 : bool) = bool_gen () in
    if b1 then []
    else
      let (size1 : int) = size - 1 in
      let (l : int list) = sized_list_gen size1 in
      let (n : int) = int_gen () in
      n :: l
