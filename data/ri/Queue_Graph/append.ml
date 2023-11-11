let rec append (hd : Node.t) (x : Elem.t) : unit =
  if hasNodeContent hd then
    if hasConnectOut hd then ()
    else
      let (c : Node.t) = newNode () in
      if hasConnectIn c then (
        append hd x;
        ())
      else if node_eq hd c then (
        append hd x;
        ())
      else (
        connect hd c;
        putNodeContent c x;
        ())
  else (
    putNodeContent hd x;
    ())

let[@assertRty] append ((n : Node.t) [@ghost]) ?l:(hd = (true : [%v: Node.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI n; res = (true : [%v: unit]); post = rI n }
