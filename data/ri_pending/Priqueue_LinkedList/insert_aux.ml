let rec insert_aux (cur : Elem.t) (x : Elem.t) : unit =
  if elem_eq cur x then ()
  else if hasNext cur then
    let (next : Elem.t) = getNext cur in
    if elem_lt cur x then (
      insert_aux next x;
      ())
    else (
      delNext cur;
      setNext x next;
      insert_aux next cur;
      ())
  else (
    setNext cur x;
    ())

let[@assertRty] insert_aux ?l:(idx = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
