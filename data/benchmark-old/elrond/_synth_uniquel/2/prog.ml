let rec goal (size : int) (x0 : int) =
  (if sizecheck size then Unil else (subs size) +:: (x0 +:: Unil) : int ulist)
