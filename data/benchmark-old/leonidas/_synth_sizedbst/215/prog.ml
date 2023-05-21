let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one hi
   then Node ((increment s0), Leaf, (goal hi (increment d) lo hi))
   else goal (increment hi) d1 d (increment d) : int tree)
