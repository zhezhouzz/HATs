let rec goal (size : int) (x0 : int) =
  (if sizecheck size then Unil else (subs size) +:: Unil : int ulist)
