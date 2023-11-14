let is_empty (c : Cell.t) : bool = if existsE c then true else false

let[@assertRty] is_empty ((a : Cell.t) [@ghost]) ?l:(x = (true : [%v: Cell.t]))
    =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }
