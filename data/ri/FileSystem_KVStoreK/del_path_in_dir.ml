let del_path_in_dir (path : Path.t) (path' : Path.t) : unit =
  if exists path then (
    let (bytes : Bytes.t) = get path in
    put path (delChild bytes path');
    ())
  else ()

let[@assertRty] del_path_in_dir ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) ?l:(path' = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }
