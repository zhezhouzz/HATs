let add_path_in_dir (path : Path.t) (path' : Path.t) : unit =
  if mem path then (
    let (bytes : Bytes.t) = get path in
    put path (addChild bytes path');
    ())
  else ()

let[@assertRty] add_path_in_dir ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) ?l:(path' = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }
