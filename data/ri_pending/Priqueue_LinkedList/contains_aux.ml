let rec contains_aux (cur : Elem.t) (x : Elem.t) : bool =
  if elem_eq cur x then true
  else if hasNext cur then
    let (next : Elem.t) = getNext cur in
    let (res : bool) = contains_aux next x in
    res
  else false

let[@assertRty] contains_aux ?l:(idx = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }
