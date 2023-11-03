let delete (path : Path.t) : bool =
  if not (mtree_mem path) then false
  else
    let (bytes : Bytes.t) = mtree_get path in
    if isDir bytes then false
    else
      let (parent_path : Path.t) = getParent path in
      let (bytes' : Bytes.t) = mtree_get parent_path in
      mtree_put path (setDeleted bytes);
      mtree_put parent_path (deleteChild bytes' path);
      true

let[@assertRty] delete ((p1 : Path.t) [@ghost]) ((p2 : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) =
  { pre = rI p1 p2; res = (true : [%v: bool]); post = rI p1 p2 }
