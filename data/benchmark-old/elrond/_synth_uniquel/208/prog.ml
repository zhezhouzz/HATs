let rec goal (size : int) (x0 : int) =
  (if sizecheck x0
   then x0 +:: (goal size x0)
   else (subs size) +:: (x0 +:: Unil) : int ulist)
