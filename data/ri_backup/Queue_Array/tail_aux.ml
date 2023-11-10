let rec tail_aux (idx : int) : unit =
  if isInited () then
    if isWritten () then
      let (tid : int) = read () in
      if idx + 1 < tid then (
        let (elem : Elem.t) = select idx in
        let (idx' : int) = idx + 1 in
        update idx' elem;
        tail_aux idx';
        ())
      else ()
    else ()
  else ()

let[@assertRty] tail_aux ((i : int) [@ghost]) ?l:(x = (true : [%v: int])) =
  { pre = rI i; res = (true : [%v: unit]); post = rI i }
