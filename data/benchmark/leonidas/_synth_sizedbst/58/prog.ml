let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then Node ((increment lo), (goal d1 s0 hi hi), (goal d1 s0 hi hi))
   else
     if bool_gen ()
     then goal (increment s0) (increment lo) d (increment s)
     else Node ((increment hi), Leaf, Leaf) : int tree)
