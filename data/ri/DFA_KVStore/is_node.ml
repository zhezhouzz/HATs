let is_node (x : Node.t) : bool = true

let[@assertRty] is_node ((s1 : Node.t) [@ghost]) ((c : Char.t) [@ghost])
    ?l:(x = (true : [%v: Node.t])) =
  { pre = rI s1 c; res = (true : [%v: bool]); post = rI s1 c }
