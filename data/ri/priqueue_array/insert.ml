let insert (x : Elem.t) : bool =
  let (res : bool) = insert_aux 0 x in
  res

let[@libRty] insert_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }

let[@assertRty] insert ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }
