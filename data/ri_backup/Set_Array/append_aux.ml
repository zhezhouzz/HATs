let appendix_aux (x : Elem.t) : unit =
  if isInited () then
    let (len : int) = size () in
    let (tid : int) = read () in
    if tid < len then (
      update tid x;
      write (tid + 1);
      ())
    else ()
  else ()

let[@libRty] append_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
