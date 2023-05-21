let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one lo
   then Node (lo, Leaf, Leaf)
   else Node ((increment d), Leaf, Leaf) : int tree)
