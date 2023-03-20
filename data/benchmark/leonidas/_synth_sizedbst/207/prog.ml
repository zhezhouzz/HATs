let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one hi
   then
     Node
       ((increment lo), (goal (increment lo) d (increment d) hi),
         (goal (increment s0) (increment d) (int_gen ()) (increment lo)))
   else goal (increment hi) d1 d (increment d) : int tree)
