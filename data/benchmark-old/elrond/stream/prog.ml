let rec stream_gen (size : int) : int stream =
  let (b : bool) = size == 0 in
  if b then Streamnil
  else
    let (b1 : bool) = bool_gen () in
    if b1 then Streamnil
    else
      let (size1 : int) = size - 1 in
      let (l : int stream) = stream_gen size1 in
      let (l2 : int stream lazyty) = Lazyty l in
      let (n : int) = int_gen () in
      Streamlazycons (n, l2)
