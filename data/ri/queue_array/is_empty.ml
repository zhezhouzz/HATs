let is_empty (u : unit) : bool =
  if isInited () then
    let (tid : int) = read () in
    if tid == 0 then true else false
  else true

let[@assertRty] is_empty ((i : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  { pre = rI i; res = (true : [%v: bool]); post = rI i }
