let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one s0
   then goal (increment d) (increment d) (increment lo) (increment d)
   else goal (increment d) d s0 (increment lo) : int tree)