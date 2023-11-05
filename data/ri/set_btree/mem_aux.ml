let rec mem_aux (cur : Elem.t) (x : Elem.t) : bool =
  if elem_eq cur x then true
  else if elem_lt x cur then
    if has_left cur then
      let (left : Elem.t) = get_left cur in
      let (res : bool) = mem_aux left x in
      res
    else false
  else if has_right cur then
    let (right : Elem.t) = get_right cur in
    let (res : bool) = mem_aux right x in
    res
  else false

let[@assertRty] mem_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI && memP cur; res = (true : [%v: bool]); post = rI }
