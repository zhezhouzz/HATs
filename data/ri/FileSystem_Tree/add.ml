let add (path : Path.t) (content : Bytes.t) : bool =
  if mem path then false
  else
    let (parent_path : Path.t) = getParent path in
    let (bytes' : Bytes.t) = get parent_path in
    if isDir bytes' then (
      connectChild parent_path path;
      put path content;
      add_path_in_dir parent_path path;
      true)
    else false

let[@libRty] add_path_in_dir ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) ?l:(path' = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }

let[@assertRty] add ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    ?l:(content = (true : [%v: Bytes.t])) =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
