let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one d
   then
     Node
       ((increment d1), (goal d1 (increment d) (increment s0) hi),
         (goal d1 (increment d1) lo hi))
   else
     if bool_gen ()
     then goal (increment s0) s0 (increment d1) (increment lo)
     else
       Node
         ((increment s), (goal (increment lo) d hi hi),
           (goal (increment lo) d hi hi)) : int tree)
