let delete (path : Path.t) : bool =
  if isRoot path then false
  else if not (exists path) then false
  else
    let (bytes : Bytes.t) = get path in
    if isDir bytes then deleteChildren path;
    let (parent_path : Path.t) = getParent path in
    let (bytes' : Bytes.t) = get parent_path in
    put path (setDeleted bytes);
    put parent_path (delChild bytes' path);
    true

let[@libRty] deleteChildren ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }

let[@assertRty] delete ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
