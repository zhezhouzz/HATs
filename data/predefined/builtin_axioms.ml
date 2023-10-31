let[@axiom] bytes1 ((content [@forall]) : int) =
  implies (is_deleted content) (not (is_dir content))

let[@axiom] path1 ((path [@forall]) : int) =
  iff (is_root path) (path == parent path)
