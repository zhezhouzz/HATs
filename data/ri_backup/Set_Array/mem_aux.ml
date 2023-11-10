let rec mem_aux (idx : int) (x : Elem.t) : bool =
  if isInited () then
    let (len : int) = read () in
    if idx < len then
      let (a : Elem.t) = select idx in
      if elem_eq x a then true
      else
        let (res : bool) = mem_aux (idx + 1) x in
        res
    else false
  else false

let[@assertRty] mem_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }
