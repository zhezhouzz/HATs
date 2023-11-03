let init (u : unit) : unit =
  let (_ : unit) = put (getRoot ()) (fileInit ()) in
  ()

let[@assertRty] init ((p1 : Path.t) [@ghost]) ((p2 : Path.t) [@ghost])
    ?l:(u = (true : [%v: unit])) =
  { pre = rI p1 p2; res = (true : [%v: unit]); post = rI p1 p2 }
