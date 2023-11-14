let is_empty (hd : Cell.t) : bool =
  if isCell hd then if hasCellContent hd then false else true else true

let[@assertRty] is_empty ?l:(hd = (true : [%v: Cell.t])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }
