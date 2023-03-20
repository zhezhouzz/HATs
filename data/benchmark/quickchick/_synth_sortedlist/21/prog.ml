let rec goal (size : int) (x0 : int) =
  (if sizecheck x0 then [x0] else goal (subs size) (gt_eq_int_gen x0) : 
  int list)
