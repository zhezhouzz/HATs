type effect = Dummy of (int -> int -> int)

let x = perform (Dummy (2, 3))
