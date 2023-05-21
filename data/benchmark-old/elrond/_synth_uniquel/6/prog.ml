let rec goal (size : int) (x0 : int) =
  (if sizecheck size then Unil else x0 +:: (x0 +:: (goal (subs size) x0)) : 
  int ulist)
