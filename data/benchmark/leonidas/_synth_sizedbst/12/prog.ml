let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node
       ((increment d1), (goal d1 (increment d) (increment s0) hi),
         (goal d1 (increment d1) lo hi))
   else
     if bool_gen ()
     then goal (increment d) (increment s) d1 (increment d1)
     else Node (d, Leaf, (goal (increment lo) d (increment hi) hi)) : 
  int tree)
