let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one lo
   then Node ((increment s0), Leaf, Leaf)
   else Node ((increment lo), Leaf, (goal d1 d1 hi hi)) : int tree)
