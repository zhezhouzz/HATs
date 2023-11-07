let rec insert_aux (cur : Elem.t) (x : Elem.t) : unit =
  if elem_eq cur x then ()
  else if elem_lt x cur then
    if has_left cur then (
      let (left : Elem.t) = get_left cur in
      insert_aux left x;
      ())
    else (
      add_left cur x;
      ())
  else if has_right cur then (
    let (right : Elem.t) = get_right cur in
    insert_aux right x;
    ())
  else (
    add_right cur x;
    ())

let[@assertRty] insert_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI && memP cur; res = (true : [%v: unit]); post = rI }
