let insert (x : Elem.t) : unit =
  if hasHead () then (
    let (hd : Elem.t) = getHead () in
    let (res : Elem.t) = insert_aux hd x in
    setHead res;
    ())
  else (
    setHead x;
    ())

let[@libRty] insert_aux ?l:(idx = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }

let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
