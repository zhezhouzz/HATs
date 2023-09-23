type t = Fa | Ex

let is_forall = function Fa -> true | Ex -> false
let is_exists x = not @@ is_forall x

let of_string = function
  | "forall" -> Fa
  | "exists" -> Ex
  | _ -> failwith "not a quantifier"

let to_string = function Fa -> "forall" | Ex -> "exists"
let pretty_layout = function Fa -> "∀ " | Ex -> "∃ "
