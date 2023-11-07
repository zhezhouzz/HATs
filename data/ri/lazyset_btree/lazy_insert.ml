let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  if hasRoot () then (
    let (root : Elem.t) = getRoot () in
    insert_aux root x;
    ())
  else (
    putRoot x;
    ())

let[@libRty] insert_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI && memP cur; res = (true : [%v: unit]); post = rI }

let[@assertRty] lazy_insert ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI; res = (true : [%v: unit]); post = rI })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
