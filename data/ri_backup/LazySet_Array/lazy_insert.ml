let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  insert_aux 0 x;
  ()

let[@libRty] insert_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }

let[@assertRty] lazy_insert ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI i a; res = (true : [%v: unit]); post = rI i a })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
