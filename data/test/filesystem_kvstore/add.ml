let add (path : Path.t) (content : Bytes.t) : bool =
  if exists path then false
  else
    let (parent_path : Path.t) = getParent path in
    if not (exists parent_path) then false
    else
      let (bytes' : Bytes.t) = get parent_path in
      true

let[@assertRty] add ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    ?l:(content = (true : [%v: Bytes.t])) =
  { pre = _G (Any true); res = (true : [%v: bool]); post = _G (Any true) }
