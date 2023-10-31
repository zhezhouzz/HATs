let[@libRty] parent ?l:(a = (true : [%v: int]) [@over]) : [%v: int] =
  v == a / 10

let[@libRty] addChild ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a + 2

let[@libRty] isRoot ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a == 0)

let[@libRty] isDeleted ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a < 0)

let[@libRty] isDir ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a mod 2 == 0 && a >= 0)
