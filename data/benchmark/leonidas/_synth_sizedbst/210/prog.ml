let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one hi
   then
     Node
       ((increment hi), (goal (increment lo) d s0 hi),
         (goal (increment hi) d s0 s))
   else goal (increment lo) (increment s) (increment s0) (increment hi) : 
  int tree)
