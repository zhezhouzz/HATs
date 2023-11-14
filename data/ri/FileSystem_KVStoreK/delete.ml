let delete (path : Path.t) : bool =
  if not (exists path) then false
  else
    let (bytes : Bytes.t) = get path in
    if isDir bytes then deleteChildren path;
    let (parent_path : Path.t) = getParent path in
    put path (setDeleted bytes);
    del_path_in_dir parent_path path;
    true

let[@libRty] del_path_in_dir ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) ?l:(path' = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }

let[@libRty] deleteChildren ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }

let[@assertRty] delete ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
