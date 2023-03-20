let rec goal (s0 : int) =
  (if bool_gen () then goal (int_gen ()) else goal (subs s0) : int tree)
