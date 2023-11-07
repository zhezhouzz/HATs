let add_node (x : Node.t) : bool =
  if isNode x then false
  else (
    addNode x;
    true)

let[@assertRty] add_node ((s1 : Node.t) [@ghost]) ((c : Char.t) [@ghost])
    ((s2 : Node.t) [@ghost]) ?l:(x = (true : [%v: Node.t])) =
  { pre = rI s1 c s2; res = (true : [%v: bool]); post = rI s1 c s2 }
