let rec insert_aux (idx : int) (x : Elem.t) : unit =
  if isInited () then
    let (bound : int) = read () in
    if idx < bound then
      let (y : Elem.t) = select idx in
      if elem_eq x y then ()
      else if elem_lt x y then (
        update idx x;
        insert_aux (idx + 1) y;
        ())
      else (
        insert_aux (idx + 1) x;
        ())
    else if idx == bound then (
      append_aux x;
      ())
    else ()
  else ()

let[@libRty] append_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }

let[@assertRty] insert_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
