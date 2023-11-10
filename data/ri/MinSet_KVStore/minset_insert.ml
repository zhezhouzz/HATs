let rec minset_insert (x : Elem.t) : unit =
  if isWritten () then
    if hasValue x then ()
    else
      let (k : Key.t) = randomKey () in
      if exists k then (
        minset_insert x;
        ())
      else
        let (min : Elem.t) = read () in
        if elem_lt x min then ()
        else (
          put k x;
          ())
  else ()

let[@assertRty] minset_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
