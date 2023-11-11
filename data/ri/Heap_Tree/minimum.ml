let rec minimum (default : Elem.t) : Elem.t =
  if hasRoot () then
    let (root : Elem.t) = getRoot () in
    let (res : Elem.t) = minimum_aux root in
    res
  else default

let[@libRty] minimum_aux ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }

let[@assertRty] minimum ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
