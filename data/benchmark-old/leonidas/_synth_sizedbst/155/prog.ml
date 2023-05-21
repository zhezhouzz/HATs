let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one lo
   then Node ((increment s), Leaf, Leaf)
   else Node ((increment d), Leaf, Leaf) : int tree)
