let minset_mem (x : Elem.t) : bool =
  let (res : bool) = mem x in
  res

let[@assertRty] minset_mem ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: bool]); post = rI m }
