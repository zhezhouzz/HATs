let[@libRty] parent ?l:(a = (true : [%v: int]) [@over]) : [%v: int] =
  v == parent a

let[@libRty] addChild ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == add_child a b

let[@libRty] isRoot ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  v == is_root a

let[@libRty] isDeleted ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  v == is_deleted a

let[@libRty] isDir ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  v == is_dir a
