let rec goal (size : int) (x0 : int) =
  (if sizecheck x0 then x0 +:: Unil else (subs size) +:: Unil : int ulist)
