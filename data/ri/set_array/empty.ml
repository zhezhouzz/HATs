let empty (len : int) : unit =
  if isInited () then ()
  else (
    init len;
    write 0;
    ())

let[@assertRty] empty ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(len = (true : [%v: int])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
