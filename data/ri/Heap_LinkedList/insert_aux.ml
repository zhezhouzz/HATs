let rec insert_aux (cur : Elem.t) (x : Elem.t) : Elem.t =
  if elem_eq cur x then cur
  else if elem_lt x cur then (
    setNext x cur;
    x)
  else if hasNext cur then
    let (next : Elem.t) = getNext cur in
    let (res : Elem.t) = insert_aux next x in
    res
  else (
    setNext cur x;
    cur)

let[@assertRty] insert_aux ?l:(idx = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
