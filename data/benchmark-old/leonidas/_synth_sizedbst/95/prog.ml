let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node (hi, (goal d1 d1 hi hi), (goal d1 (increment d) (increment s0) hi))
   else
     if bool_gen ()
     then goal (increment s0) (increment lo) d (increment s)
     else Node (n, Leaf, (goal (increment lo) (increment d1) hi hi)) : 
  int tree)
