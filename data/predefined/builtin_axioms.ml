let[@axiom] path1 ((content [@forall]) : int) =
  implies (is_deleted content) (not (is_dir content))
