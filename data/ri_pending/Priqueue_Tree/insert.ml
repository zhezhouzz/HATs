let insert (x : Elem.t) : unit =
  if hasRoot () then (
    let (root : Elem.t) = getRoot () in
    insert_aux root x;
    ())
  else (
    putRoot x;
    ())

let[@libRty] insert_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI && memP cur; res = (true : [%v: unit]); post = rI }

let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
