let rec minset_insert (x : Elem.t) : unit =
  if has_value x then ()
  else
    let (k : Key.t) = random_key () in
    if exists k then (
      minset_insert x;
      ())
    else (
      put k x;
      if isWritten () then
        let (min : Elem.t) = read () in
        if elem_lt x min then (
          write x;
          ())
        else ()
      else (
        write x;
        ()))

let[@assertRty] minset_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
