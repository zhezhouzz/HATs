let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one lo then Node (n, Leaf, Leaf) else Node (s0, Leaf, Leaf) : 
  int tree)
