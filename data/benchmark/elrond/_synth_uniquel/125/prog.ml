let rec goal (size : int) (x0 : int) =
  (if sizecheck x0 then (subs size) +:: Unil else goal (subs size) x0 : 
  int ulist)
