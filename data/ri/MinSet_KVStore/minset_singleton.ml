let rec minset_singleton (x : Elem.t) : bool =
  if isWritten () then false
  else
    let (k : Key.t) = randomKey () in
    if exists k then
      let (res : bool) = minset_singleton x in
      res
    else (
      write x;
      put k x;
      true)

let[@assertRty] minset_singleton ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: bool]); post = rI m }
