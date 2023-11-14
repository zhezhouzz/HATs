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
  is_dir v

let[@libRty] delChild ?l:(a = (true : [%v: Bytes.t]) [@over])
    ?l:(b = (true : [%v: Path.t]) [@over]) : [%v: Bytes.t] =
  is_dir v

let[@libRty] getChild ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: Path.t] =
  true

let[@libRty] hasChild ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: bool] =
  true

(* let[@libRty] isDeleted ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: bool] = *)
(*   v == is_deleted a *)

let[@libRty] setDeleted ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: Bytes.t]
    =
  is_dir v
(* not (is_dir v) *)
(* is_del v *)

let[@libRty] isDir ?l:(a = (true : [%v: Bytes.t]) [@over]) : [%v: bool] =
  v == is_dir a
