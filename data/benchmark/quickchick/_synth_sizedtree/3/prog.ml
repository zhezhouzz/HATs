let rec goal (s0 : int) =
  (if sizecheck s0
   then Leaf
   else if bool_gen () then goal (subs s0) else goal (subs s0) : int tree)
