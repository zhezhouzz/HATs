let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node (s, (goal d1 (increment d) (increment s0) hi), (goal d1 s0 hi hi))
   else
     if bool_gen ()
     then goal (increment d) (increment s) d1 (increment d1)
     else Node (n, Leaf, (goal (increment lo) (increment d1) hi hi)) : 
  int tree)
