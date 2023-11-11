let rec minimum_aux (root : Elem.t) : Elem.t =
  if hasLeft root then
    let (left : Elem.t) = getLeft root in
    let (res : Elem.t) = minimum_aux left in
    res
  else root

let[@assertRty] minimum_aux ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
