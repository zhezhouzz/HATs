let rec head (default : Elem.t) (s : Cell.t) : unit =
  if exists s then
    let (x : Elem.t) = getElem s in
    x
  else default
