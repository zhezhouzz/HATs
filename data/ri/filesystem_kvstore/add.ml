let[@pred] rI (p : Path.t) =
  _G (Any (is_root p))
  || _G (not (Put ((p [@d]), x_1, v, true)))
  || _U (not (Put ((p [@d]), x_1, v, true))) (mkdirP (parent p))

let add (path : Path.t) (content : Bytes.t) : bool =
  if exists path then false
  else
    let (parent_path : Path.t) = getParent path in
    if not (exists parent_path) then false
    else
      let (bytes' : Bytes.t) = get parent_path in
      if isDir bytes' then (
        put path content;
        put parent_path (addChild bytes' path);
        true)
      else false

let[@assertRty] add ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    ?l:(content = (true : [%v: Bytes.t])) =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
