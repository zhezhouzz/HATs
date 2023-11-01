let[@pred] rI (p : int) =
  _G (Any (is_root p))
  || _G (not (Put ((p [@d]), x_1, v, true)))
  || _U (not (Put ((p [@d]), x_1, v, true))) (mkdirP (parent p))

let delete (path : int) : bool =
  if not (exists path) then false
  else
    let (bytes : int) = get path in
    if isDir bytes then false
    else
      let (parent_path : int) = getParent path in
      (* let (bytes' : int) = get parent_path in *)
      put path (setDeleted bytes);
      (* put parent_path (deleteChild bytes' path); *)
      true

let[@assertRty] delete ((p : int) [@ghost]) ?l:(path = (true : [%v: int])) =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
