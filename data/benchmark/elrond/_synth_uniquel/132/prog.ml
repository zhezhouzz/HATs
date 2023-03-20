let rec goal (size : int) (x0 : int) =
  (if sizecheck x0
   then (subs size) +:: Unil
   else (subs size) +:: (goal (subs size) x0) : int ulist)
