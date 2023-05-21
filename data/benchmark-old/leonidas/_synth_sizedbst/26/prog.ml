let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node (s, (goal d1 (increment d) (increment s0) hi), (goal d1 s0 hi hi))
   else
     if bool_gen ()
     then goal (increment s0) s0 (increment d1) (increment lo)
     else
       Node
         ((increment s0), (goal (increment lo) d hi hi),
           (goal (increment lo) (increment d1) hi hi)) : int tree)
