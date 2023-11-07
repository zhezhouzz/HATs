let tail (u : unit) : unit =
  if isInited () then
    if isWritten () then
      let (tid : int) = read () in
      if tid == 0 then ()
      else if tid == 1 then (
        write (tid - 1);
        ())
      else (
        (* tail_aux 0; *)
        write (tid - 1);
        ())
    else ()
  else ()

let[@libRty] tail_aux ((i : int) [@ghost]) ?l:(x = (true : [%v: int])) =
  { pre = rI i; res = (true : [%v: unit]); post = rI i }

let[@assertRty] tail ((i : int) [@ghost]) ?l:(x = (true : [%v: unit])) =
  { pre = rI i; res = (true : [%v: unit]); post = rI i }
