let rec goal (size : int) =
  (if sizecheck size
   then []
   else if bool_gen () then goal (subs size) else goal (subs size) : 
  int list)
