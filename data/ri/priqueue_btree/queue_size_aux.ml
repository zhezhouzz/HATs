let rec queue_size_aux (cur : Elem.t) : int =
  let (size1 : int) =
    if has_left cur then
      let (left : Elem.t) = get_left cur in
      let (size_l : int) = queue_size_aux left in
      size_l
    else 0
  in
  let (size2 : int) =
    if has_right cur then
      let (right : Elem.t) = get_right cur in
      let (size_r : int) = queue_size_aux right in
      size_r
    else 0
  in
  let (res : int) = 1 + size1 + size2 in
  res

let[@assertRty] queue_size_aux ?l:(cur = (true : [%v: Elem.t])) =
  { pre = rI && memP cur; res = (true : [%v: int]); post = rI }
