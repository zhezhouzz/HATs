let batchedq_gen (sizel : int) : int batchedq =
  let (sizer : int) = int_range_inc 0 sizel in
  let (l1 : int list) = list_gen sizel in
  let (l2 : int list) = list_gen sizer in
  Batchedq (l1, l2)
