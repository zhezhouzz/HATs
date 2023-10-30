let add (path : int) (content : int) : bool =
  if exists path then false
  else
    let (parent_path : int) = parent path in
    if not (exists parent_path) then false
    else
      let (bytes' : int) = get parent_path in
      if isDir bytes' then (
        put path content;
        put parent_path (addChild bytes' path);
        true)
      else false

let[@assertRty] add ?l:(path = (true : [%v: int]))
    ?l:(content = (true : [%v: int])) =
  { pre = _G (Any true); res = (true : [%v: bool]); newadding = _G (Any true) }

(* let[@assertRty] add ?l:(path = (true : [%v: int])) *)
(*     ?l:(content = (true : [%v: int])) = *)
(*   { pre = _G (Any true); res = (true : [%v: bool]); newadding = _G (Any true) } *)
