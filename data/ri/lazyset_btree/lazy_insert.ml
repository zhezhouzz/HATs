let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  if has_root () then (
    let (root : Elem.t) = get_root () in
    insert_aux root x;
    ())
  else (
    put_root x;
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
