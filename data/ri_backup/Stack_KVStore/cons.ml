let rec cons (x : Elem.t) (s : Cell.t) : Cell.t =
  let (c : Cell.t) = newCell () in
  if exists c then
    let (c' : Cell.t) = cons () in
    c'
  else (
    put c x s;
    c)
