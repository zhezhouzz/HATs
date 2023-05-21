let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node (s, (goal d1 (increment d) (increment s0) hi), (goal d1 s0 hi hi))
   else
     if bool_gen ()
     then goal (increment s) (increment lo) (increment d) (increment s)
     else Node (d, Leaf, (goal (increment lo) d (increment hi) hi)) : 
  int tree)
