let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node (lo, (goal d1 s0 hi hi), (goal d1 d1 (increment hi) (increment d)))
   else
     if bool_gen ()
     then goal (increment s0) s0 (increment d1) (increment lo)
     else
       Node
         ((increment s0), (goal (increment lo) d hi hi),
           (goal (increment lo) (increment d1) hi hi)) : int tree)
