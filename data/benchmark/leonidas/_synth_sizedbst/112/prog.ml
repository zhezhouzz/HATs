let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one s0
   then goal (increment s0) (increment hi) d (increment s)
   else goal (increment lo) d (increment hi) (increment d1) : int tree)
