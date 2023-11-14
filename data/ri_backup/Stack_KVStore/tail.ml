let rec tail (s : Cell.t) : Cell.t =
  if exists s then
    let (s' : Cell.t) = getCell s in
    s'
  else s
