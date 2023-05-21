let rec goal (s0 : int) =
  (if sizecheck s0
   then Leaf
   else
     if bool_gen ()
     then goal (subs s0)
     else Node ((subs s0), (goal s01), (goal s01)) : int tree)
