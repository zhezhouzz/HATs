let insert (x : Elem.t) : bool =
  let (res : bool) = insert_aux 0 x in
  res

let[@libRty] insert_aux ((a : Elem.t) [@ghost]) ?l:(idx = (true : [%v: int]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }

let[@assertRty] insert ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }
