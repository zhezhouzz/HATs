let tail (hd : Cell.t) : Cell.t =
  if hasNext hd then
    let (hd' : Cell.t) = getNext hd in
    hd'
  else hd

let[@assertRty] tail ?l:(hd = (true : [%v: Cell.t])) =
  { pre = rI; res = (true : [%v: Cell.t]); post = rI }
