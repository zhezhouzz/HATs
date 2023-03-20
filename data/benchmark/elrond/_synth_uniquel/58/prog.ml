let rec goal (size : int) (x0 : int) =
  (if sizecheck x0
   then (subs size) +:: (x0 +:: (goal size x0))
   else x0 +:: Unil : int ulist)
