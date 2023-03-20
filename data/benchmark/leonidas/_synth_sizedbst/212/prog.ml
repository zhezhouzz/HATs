let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one hi
   then
     Node
       ((increment hi), Leaf, (goal root root (increment s0) (increment lo)))
   else goal (increment lo) (increment s) (increment s0) (increment hi) : 
  int tree)
