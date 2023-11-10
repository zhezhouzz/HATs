let head (default : Elem.t) : Elem.t =
  if isInited () then
    let (tid : int) = read () in
    if tid == 0 then default
    else
      let (res : Elem.t) = select 0 in
      res
  else default

let[@assertRty] head ((i : int) [@ghost]) ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI i; res = (true : [%v: Elem.t]); post = rI i }
