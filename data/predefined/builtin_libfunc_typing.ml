let[@libRty] getParent ?l:(a = (true : [%v: Path.t]) [@over]) : [%v: Path.t] =
  v == parent a

let[@libRty] isRoot ?l:(a = (true : [%v: Path.t]) [@over]) : [%v: bool] =
  v == is_root a

let[@libRty] getRoot ?l:(a = (true : [%v: unit]) [@over]) : [%v: Path.t] =
  is_root v

let[@libRty] fileInit ?l:(a = (true : [%v: unit]) [@over]) : [%v: Bytes.t] =
  is_dir v

let[@libRty] addChild ?l:(a = (true : [%v: Bytes.t]) [@over])
    ?l:(b = (true : [%v: Path.t]) [@over]) : [%v: Bytes.t] =
  v == a

let[@libRty] delChild ?l:(a = (true : [%v: Bytes.t]) [@over])
    ?l:(b = (true : [%v: Path.t]) [@over]) : [%v: Bytes.t] =
  v == a

let[@libRty] getChild ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: Path.t] =
  is_child a v

let[@libRty] hasChild ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: bool] =
  iff v (has_child a)

let[@libRty] isDeleted ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: bool] =
  v == is_deleted a

let[@libRty] setDeleted ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: Bytes.t]
    =
  is_deleted v

let[@libRty] isDir ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: bool] =
  v == is_dir a
