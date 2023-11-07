let rec contains_aux (idx : int) (x : Elem.t) : bool =
  let (len : int) = size () in
  if idx < len then
    let (a : Elem.t) = select idx in
    if elem_eq x a then true
    else
      let (res : bool) = contains_aux (idx + 1) x in
      res
  else false

let[@assertRty] contains_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }
