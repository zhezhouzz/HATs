let[@axiom] path1 ((content [@forall]) : int) =
  implies (is_deleted content) (not (id_dir content))
