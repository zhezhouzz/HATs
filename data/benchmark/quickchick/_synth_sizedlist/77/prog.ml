let rec goal (size : int) =
  (if sizecheck size
   then []
   else
     if bool_gen ()
     then (subs (gt_eq_int_gen size)) :: (subs size) :: (goal (subs size))
     else n :: (goal (subs (gt_eq_int_gen size))) : int list)
