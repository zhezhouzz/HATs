let head (default : Elem.t) (hd : Cell.t) : Elem.t =
  if hasCellContent hd then
    let (res : Elem.t) = getCellContent hd in
    res
  else default

let[@assertRty] head ?l:(default = (true : [%v: Elem.t]))
    ?l:(hd = (true : [%v: Cell.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
