let head (default : Elem.t) (hd : Node.t) : Elem.t =
  if hasNodeContent hd then
    let (res : Elem.t) = getNodeContent hd in
    res
  else default

let[@assertRty] head ((n : Node.t) [@ghost])
    ?l:(default = (true : [%v: Elem.t])) ?l:(hd = (true : [%v: Node.t])) =
  { pre = rI n; res = (true : [%v: Elem.t]); post = rI n }
