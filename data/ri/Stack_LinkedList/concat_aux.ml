let rec concat_aux (s1 : Cell.t) (s2 : Cell.t) : unit =
  if hasNext s1 then (
    let (s1' : Cell.t) = getNext s1 in
    concat_aux s1' s2;
    ())
  else if hasPrev s2 then ()
  else if cell_eq s1 s2 then ()
  else (
    setNext s1 s2;
    ())

let[@assertRty] concat_aux ?l:(s1 = (true : [%v: Cell.t]))
    ?l:(s2 = (true : [%v: Cell.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
