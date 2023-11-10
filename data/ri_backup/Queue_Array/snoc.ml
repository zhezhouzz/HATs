let snoc (x : Elem.t) : unit =
  if isInited () then
    let (tid : int) = read () in
    let (len : int) = size () in
    if tid < len then ()
    else (
      update tid x;
      write (tid + 1);
      ())
  else ()

let[@assertRty] snoc ((i : int) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i; res = (true : [%v: unit]); post = rI i }
