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

let[@libRty] eqn ?l:(a = (true : [%v: nat]) [@over])
    ?l:(b = (true : [%v: nat]) [@over]) : [%v: bool] =
  iff v (a == b)

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

let[@libRty] parent ?l:(a = (true : [%v: int]) [@over]) : [%v: int] =
  v == a / 10

let[@libRty] isDir ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a mod 2 == 0)

let[@libRty] addChild ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a + 2
