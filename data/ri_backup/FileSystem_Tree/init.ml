let init (u : unit) : unit =
  let (_ : unit) = put (getRoot ()) (fileInit ()) in
  ()

let[@assertRty] init ((p : Path.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }
