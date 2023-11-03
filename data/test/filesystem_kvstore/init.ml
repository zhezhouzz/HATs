let[@pred] rI (p : Path.t) =
  _G (Any (is_root p))
  || _G (not (Put ((p [@d]), x_1, v, true)))
  || _U (not (Put ((p [@d]), x_1, v, true))) (mkdirP (parent p))

let init (u : unit) : unit =
  let (_ : unit) = put (getRoot ()) (fileInit ()) in
  ()

let[@assertRty] init ((p : Path.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }
