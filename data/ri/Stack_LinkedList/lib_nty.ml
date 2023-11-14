val newCell : unit -> Cell.t
val isCell : Cell.t -> bool
val hasCellContent : Cell.t -> bool
val putCellContent : Cell.t -> Elem.t -> unit
val getCellContent : Cell.t -> Elem.t
val setNext : Cell.t -> Cell.t -> unit
val hasNext : Cell.t -> bool
val hasPrev : Cell.t -> bool
val getNext : Cell.t -> Cell.t
