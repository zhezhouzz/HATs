let is_node (x : Node.t) : bool =
  let (res : bool) = isNode x in
  res

let[@assertRty] is_node ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ((c : Color.t) [@ghost]) ?l:(x = (true : [%v: Node.t])) =
  { pre = rI s1 s2 c; res = (true : [%v: bool]); post = rI s1 s2 c }
