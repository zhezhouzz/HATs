let rec tail (hd : Node.t) : Node.t =
  if hasConnectOut hd then
    let (hd' : Node.t) = newNode () in
    if isConnected hd hd' then hd'
    else
      let (res : Node.t) = tail hd in
      res
  else hd

let[@assertRty] tail ((n : Node.t) [@ghost]) ?l:(hd = (true : [%v: Node.t])) =
  { pre = rI n; res = (true : [%v: Node.t]); post = rI n }
