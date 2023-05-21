let gen_const (a : unit) : stlc_term =
  let (n2 : int) = nat_gen () in
  Stlc_const n2
