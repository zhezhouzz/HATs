let rec mem (x : Elem.t) : bool =
  let (res : bool) = has_value x in
  res

let[@assertRty] mem ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }
