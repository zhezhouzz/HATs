let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one s0
   then goal (increment d) (increment d) (increment lo) (increment d)
   else goal (increment s) (increment hi) d1 (increment d) : int tree)
