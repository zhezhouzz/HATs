let rec mem (x : Elem.t) : bool =
  let (res : bool) = mem_aux 0 x in
  res

let[@libRty] mem_aux ((a : Elem.t) [@ghost]) ?l:(idx = (true : [%v: int]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }

let[@assertRty] mem ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }
