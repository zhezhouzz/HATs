(* let[@pred] headP (value : Cell.t) = *)
(*   _F (SetHead ((value [@d]), v, true) && _X (_G (not (SetHead (x_0, v, true))))) *)

(* let[@pred] has_headP (k : Cell.t) = _F (SetHead (x_0, v, true)) *)

let[@pred] nextP (prev : Cell.t) (value : Cell.t) =
  _F
    (SetNext ((prev [@d]), (value [@d]), v, true)
    && _X (_G (not (SetNext ((prev [@d]), x_1, v, true)))))

let[@pred] has_nextP (prev : Cell.t) = _F (SetNext ((prev [@d]), x_1, v, true))
let[@pred] has_prevP (a : Cell.t) = _F (SetNext (x_0, (a [@d]), v, true))

let[@pred] storeP (c : Cell.t) (a : Elem.t) =
  _F
    (PutCellContent ((c [@d]), (a [@d]), v, true)
    && _X (_G (not (PutCellContent ((c [@d]), x_1, v, true)))))

let[@pred] is_storedP (c : Cell.t) =
  _F (PutCellContent ((c [@d]), x_1, v, true))

let[@pred] is_cell (c : Cell.t) = _F (NewCell (x_0, v, v == c))
