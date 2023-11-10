let rec contains (x : Elem.t) : bool =
  if hasRoot () then
    let (root : Elem.t) = getRoot () in
    if elem_eq root x then true
    else
      let (res : bool) = contains_aux root x in
      res
  else false

let[@libRty] contains_aux ?l:(idx = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }

let[@assertRty] contains ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }
