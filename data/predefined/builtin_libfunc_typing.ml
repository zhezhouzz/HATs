let[@libRty] getParent ?l:(a = (true : [%v: int]) [@over]) : [%v: int] =
  v == parent a

let[@libRty] addChild ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == add_child a b

let[@libRty] deleteChild ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == del_child a b

let[@libRty] isRoot ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  v == is_root a

let[@libRty] isDeleted ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  v == is_deleted a

let[@libRty] setDeleted ?l:(a = (true : [%v: int]) [@over]) : [%v: int] =
  is_deleted v

let[@libRty] isDir ?l:(a = (true : [%v: int]) [@over]) : [%v: bool] =
  v == is_dir a

let[@libRty] getRoot ?l:(a = (true : [%v: unit]) [@over]) : [%v: int] =
  is_root v

let[@libRty] fileInit ?l:(a = (true : [%v: unit]) [@over]) : [%v: int] =
  is_dir v
