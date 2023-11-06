let rec queue_size (u : unit) : int =
  let (res : int) = size () in
  res

let[@assertRty] queue_size ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: unit])) =
  { pre = rI i a; res = (true : [%v: int]); post = rI i a }
