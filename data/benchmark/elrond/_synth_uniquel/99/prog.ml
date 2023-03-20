let rec goal (size : int) (x0 : int) =
  (if sizecheck x0
   then (subs size) +:: (goal size x0)
   else (subs size) +:: Unil : int ulist)
