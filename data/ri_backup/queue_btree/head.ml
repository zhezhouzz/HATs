let head (default : Elem.t) : Elem.t =
  if hasRoot () then
    let (root : Elem.t) = getRoot () in
    root
  else default

let[@assertRty] head ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
