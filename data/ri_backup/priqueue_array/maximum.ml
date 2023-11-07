let rec maximum (u : unit) : Elem.t =
  let (res : Elem.t) = select 0 in
  res

let[@assertRty] maximum ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: unit])) =
  { pre = rI i a; res = (true : [%v: Elem.t]); post = rI i a }
