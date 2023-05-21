let rec goal (size : int) (x0 : int) =
  (if sizecheck size then Unil else x0 +:: (goal size x0) : int ulist)
