let rec goal (size : int) (x0 : int) =
  (if sizecheck size then [] else [subs x0] : int list)
