let rec tail (s : Cell.t) : Cell.t =
  if existsC s then
    let (s' : Cell.t) = getC s in
    s'
  else s

let[@assertRty] tail ((a : Cell.t) [@ghost]) ?l:(s = (true : [%v: Cell.t])) =
  { pre = rI a; res = (true : [%v: Cell.t]); post = rI a }
