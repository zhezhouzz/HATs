let delete (path : Path.t) : bool =
  if not (exists path) then false
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
  {
    pre = rI p;
    res = (true : [%v: unit]);
    post =
      rI p
      && not (_F (Put (x_0, x_1, v, path == parent x_0 && not (is_del x_1))))
      (* post = *)
      (* rI p *)
      (* && not *)
      (*   (_F *)
      (*      (Put (x_0, x_1, v, path == parent x_0 && not (is_del x_1)) *)
      (*       && _X *)
      (*         (_G *)
      (*            (not *)
      (*               (Put (x_0, x_1, v, path == parent x_0 && is_del x_1)))) *)
      (*      )); *);
  }

let[@assertRty] delete ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
