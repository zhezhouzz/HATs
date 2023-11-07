let rec maximum (default : Elem.t) : Elem.t =
  if isInited () then
    let (res : Elem.t) = select 0 in
    res
  else default

let[@assertRty] maximum ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: Elem.t]); post = rI i a }
