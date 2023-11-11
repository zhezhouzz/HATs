let rec snoc (hd : Node.t) (x : Elem.t) : unit =
  if hasConnectOut hd then
    let (hd' : Node.t) = newNode () in
    if isConnected hd hd' then (
      snoc hd' x;
      ())
    else (
      snoc hd x;
      ())
  else (
    append hd x;
    ())

let[@libRty] append ((n : Node.t) [@ghost]) ?l:(hd = (true : [%v: Node.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI n; res = (true : [%v: unit]); post = rI n }

let[@assertRty] snoc ((n : Node.t) [@ghost]) ?l:(hd = (true : [%v: Node.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI n; res = (true : [%v: unit]); post = rI n }
