let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  let (res : bool) = insert_aux 0 x in
  ()

let[@libRty] insert_aux ((a : Elem.t) [@ghost]) ?l:(idx = (true : [%v: int]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }

let[@assertRty] lazy_insert ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI a; res = (true : [%v: unit]); post = rI a })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI a; res = (true : [%v: unit]); post = rI a }
