let rec goal (s0 : int) =
  (if bool_gen () then goal (subs s0) else goal (subs s0) : int tree)
