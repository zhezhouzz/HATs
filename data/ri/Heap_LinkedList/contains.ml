let rec contains (x : Elem.t) : bool =
  if hasHead () then
    let (hd : Elem.t) = getHead () in
    let (res : bool) = contains_aux hd x in
    res
  else false

let[@libRty] contains_aux ?l:(idx = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }

let[@assertRty] contains ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }
