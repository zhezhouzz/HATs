let rec minimum (default : Elem.t) : Elem.t =
  if hasHead () then
    let (hd : Elem.t) = getHead () in
    hd
  else default

let[@assertRty] minimum ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
