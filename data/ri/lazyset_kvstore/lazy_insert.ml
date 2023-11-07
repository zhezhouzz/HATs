let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  if hasValue x then ()
  else (
    insert_aux x;
    ())

let[@libRty] insert_aux ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: unit]); post = rI a }

let[@assertRty] lazy_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI m; res = (true : [%v: unit]); post = rI m })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
