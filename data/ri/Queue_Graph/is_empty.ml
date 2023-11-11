let is_empty (hd : Node.t) : bool = if hasNodeContent hd then false else true

let[@assertRty] is_empty ((n : Node.t) [@ghost]) ?l:(hd = (true : [%v: Node.t]))
    =
  { pre = rI n; res = (true : [%v: bool]); post = rI n }
