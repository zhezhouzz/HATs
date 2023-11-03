let add (path : Path.t) (content : Bytes.t) : bool =
  if mem path then false
  else
    let (parent_path : Path.t) = getParent path in
    let (bytes' : Bytes.t) = get parent_path in
    if isDir bytes' then (
      connect_child parent_path path;
      put path content;
      put parent_path (addChild bytes' path);
      true)
    else false

let[@assertRty] add ((p1 : Path.t) [@ghost]) ((p2 : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) ?l:(content = (true : [%v: Bytes.t])) =
  { pre = rI p1 p2; res = (true : [%v: bool]); post = rI p1 p2 }
