let force (thunk : unit -> unit) : unit =
  thunk ();
  ()

let[@assertRty] force ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI i a; res = (true : [%v: unit]); post = rI i a }) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
