let rec goal (size : int) (x0 : int) =
  (if sizecheck size
   then []
   else (subs size) :: (goal (subs size) (gt_eq_int_gen x0)) : int list)
