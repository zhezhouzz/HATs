let rec deleteChildren (path : Path.t) : unit =
  if not (mem path) then ()
  else
    let (bytes : Bytes.t) = get path in
    if hasChild bytes then (
      let (child_path : Path.t) = getChild bytes in
      let (res' : bool) = delete child_path in
      deleteChildren path;
      ())
    else ()

let[@libRty] delete ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }

let[@assertRty] deleteChildren ((p : Path.t) [@ghost])
    ?l:(path = (true : [%v: Path.t])) =
  { pre = rI p; res = (true : [%v: unit]); post = rI p }
