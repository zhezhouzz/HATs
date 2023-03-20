let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node (lo, (goal d1 s0 hi hi), (goal d1 d1 (increment hi) (increment d)))
   else
     if bool_gen ()
     then goal (increment s) (increment lo) (increment d) (increment s)
     else Node ((increment hi), Leaf, Leaf) : int tree)
