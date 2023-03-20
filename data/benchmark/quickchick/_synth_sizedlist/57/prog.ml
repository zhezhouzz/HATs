let rec goal (size : int) =
  (if sizecheck size
   then []
   else
     if bool_gen ()
     then (subs (gt_eq_int_gen size)) :: (subs size) :: (goal (subs size))
     else goal (subs (gt_eq_int_gen (subs size))) : int list)
