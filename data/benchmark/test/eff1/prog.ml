type 'a effect =
  | Put of int * unit
  | Get of int * int
  | Dummy of ((int * int) * int) * unit

let x = perform (Dummy ((2, 3), 2))
