let minset_singleton (x : Elem.t) : bool =
  if isWritten () then false
  else (
    write x;
    insert x;
    true)

let[@assertRty] minset_singleton ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: bool]); post = rI m }
