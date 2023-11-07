let rec insert_aux (idx : int) (x : Elem.t) : bool =
  if isInited () then
    let (len : int) = size () in
    if idx < len then
      let (y : Elem.t) = select idx in
      if elem_eq x y then true
      else if elem_lt x y then (
        update idx x;
        let (res : bool) = insert_aux (idx + 1) y in
        res)
      else
        let (res : bool) = insert_aux (idx + 1) x in
        res
    else false
  else (
    init (randomLen ());
    true)

let[@assertRty] insert_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }
