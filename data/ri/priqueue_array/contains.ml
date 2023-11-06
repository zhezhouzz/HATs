let rec contains (x : Elem.t) : bool =
  let (res : bool) = contains_aux 0 x in
  res

let[@libRty] contains_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }

let[@assertRty] contains ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }
