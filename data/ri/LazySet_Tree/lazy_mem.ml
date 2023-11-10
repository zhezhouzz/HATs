let mem (x : Elem.t) (thunk : unit -> unit) (z : unit) : bool =
  thunk ();
  if hasRoot () then
    let (root : Elem.t) = getRoot () in
    if elem_eq root x then true
    else
      let (res : bool) = mem_aux root x in
      res
  else false

let[@libRty] mem_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI && memP cur; res = (true : [%v: bool]); post = rI }

let[@assertRty] mem ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI; res = (true : [%v: unit]); post = rI })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: bool]); post = rI }
