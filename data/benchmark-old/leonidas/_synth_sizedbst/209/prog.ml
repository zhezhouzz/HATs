let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one hi
   then
     Node
       ((increment d1), Leaf, (goal root root (increment s0) (increment lo)))
   else goal (increment hi) d1 d (increment d) : int tree)
