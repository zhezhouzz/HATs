let rec empty (x : unit) : Node.t =
  let (c : Node.t) = newNode () in
  if hasNodeContent c then
    let (c' : Node.t) = empty () in
    c'
  else c

let[@assertRty] empty ((n : Node.t) [@ghost]) ?l:(len = (true : [%v: unit])) =
  { pre = rI n; res = (true : [%v: Node.t]); post = rI n }
