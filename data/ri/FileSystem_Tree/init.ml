let init (u : unit) : unit =
  init (getRoot ());
  put (getRoot ()) (fileInit ());
  ()

let[@assertRty] init ((p : Path.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }
