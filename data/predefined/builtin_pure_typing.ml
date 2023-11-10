let[@libRty] ( && ) ?l:(a = (true : [%v: bool]) [@over])
    ?l:(b = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (a && b)

let[@libRty] ( || ) ?l:(a = (true : [%v: bool]) [@over])
    ?l:(b = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (a || b)

let[@libRty] not ?l:(a = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (not a)

let[@libRty] ( == ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a == b)

(* let[@libRty] eqn ?l:(a = (true : [%v: nat]) [@over]) *)
(*     ?l:(b = (true : [%v: nat]) [@over]) : [%v: bool] = *)
(*   iff v (a == b) *)

let[@libRty] ( != ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a != b)

let[@libRty] ( < ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a < b)

let[@libRty] ( > ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a > b)

let[@libRty] ( <= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a <= b)

let[@libRty] ( >= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a >= b)

let[@libRty] ( + ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a + b

let[@libRty] ( - ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a - b

let[@libRty] ( mod ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a mod b

let[@libRty] ( * ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a * b

let[@libRty] ( / ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (not (v == 0) : [%v: int]) [@over]) : [%v: int] =
  v == a / b

let[@libRty] elem_eq ?l:(a = (true : [%v: Elem.t]) [@over])
    ?l:(b = (true : [%v: Elem.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] elem_lt ?l:(a = (true : [%v: Elem.t]) [@over])
    ?l:(b = (true : [%v: Elem.t]) [@over]) : [%v: bool] =
  iff v (elem_lt a b)

let[@libRty] color_eq ?l:(a = (true : [%v: Color.t]) [@over])
    ?l:(b = (true : [%v: Color.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] node_eq ?l:(a = (true : [%v: Node.t]) [@over])
    ?l:(b = (true : [%v: Node.t]) [@over]) : [%v: bool] =
  iff v (a == b)
