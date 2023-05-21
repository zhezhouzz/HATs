let rec goal (size : int) (x0 : int) =
  (if sizecheck x0
   then (subs size) +:: (x0 +:: Unil)
   else (subs size) +:: (x0 +:: Unil) : int ulist)
