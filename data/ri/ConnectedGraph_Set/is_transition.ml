let is_transition (st : Node.t) (en : Node.t) : bool =
  if mem st en then true else false

let[@assertRty] is_transition ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ?l:(st = (true : [%v: Node.t])) ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 s2; res = (true : [%v: bool]); post = rI s1 s2 }
