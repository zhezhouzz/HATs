let[@pred] rI (p : Path.t) =
  _G (Any (is_root p))
  || _G (not (Put ((p [@d]), x_1, v, true)))
  || _U (not (Put ((p [@d]), x_1, v, true))) (mkdirP (parent p))

let delete (path : Path.t) : bool =
  if not (exists path) then false
  else
    let (bytes : Bytes.t) = get path in
    if isDir bytes then false
    else
      let (parent_path : Path.t) = getParent path in
      let (bytes' : Bytes.t) = get parent_path in
      put path (setDeleted bytes);
      put parent_path (deleteChild bytes' path);
      true

let[@assertRty] delete ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
