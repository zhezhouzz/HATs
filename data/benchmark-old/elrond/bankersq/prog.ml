let bankersq_gen (lenf : int) : int bankersq =
  let (lenr : int) = int_range_inc 0 lenf in
  let (f : int stream) = stream_gen lenf in
  let (r : int stream) = stream_gen lenr in
  Bankersq (lenf, f, lenr, r)
