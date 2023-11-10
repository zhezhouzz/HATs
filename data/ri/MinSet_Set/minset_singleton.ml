let minset_singleton (x : Elem.t) : bool =
  if isWritten () then false
  else (
    insert x;
    write x;
    true)

let[@assertRty] minset_singleton ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: bool]); post = rI m }
