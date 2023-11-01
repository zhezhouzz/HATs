let[@axiom] bytes1 ((content [@forall]) : Bytes.t) =
  implies (is_deleted content) (not (is_dir content))

let[@axiom] bytes2 ((content [@forall]) : Bytes.t) =
  implies (is_dir content) (not (is_deleted content))

(* let[@axiom] bytes3 ((content [@forall]) : int) ((path [@forall]) : int) = *)
(*   iff (is_deleted content) (is_deleted (add_child content path)) *)

(* let[@axiom] bytes4 ((content [@forall]) : int) ((path [@forall]) : int) = *)
(*   iff (is_dir content) (is_dir (add_child content path)) *)

let[@axiom] path1 ((path [@forall]) : Path.t) =
  iff (is_root path) (path == parent path)
