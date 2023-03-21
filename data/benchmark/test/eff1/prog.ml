val dummy : eff:int * int -> eff:int -> unit

let x = perform (dummy (2, 3) 2)
