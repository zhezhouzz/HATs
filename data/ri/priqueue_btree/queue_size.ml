let rec queue_size (u : unit) : int =
  if has_root () then
  else
    0

let[@assertRty] queue_size ?l:(x = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: int]); post = rI }
