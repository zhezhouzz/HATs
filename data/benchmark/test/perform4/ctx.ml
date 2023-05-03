let[@librty] mk_put =
  let[@pi] [@eff] a = ((true : [%v: int * int]) : [%h: tr]) [@over] in
  let[@pi] [@eff] b = ((true : [%v: unit]) : [%h: tr]) [@over] in
  ((len h == 0 : [%v: unit]) : [%h: tr]) [@under]

let[@librty] prog =
  let[@pi] n = ((v >= 0 : [%v: int]) : [%h: tr]) [@over] in
  ((len h == n && fun (u : [%forall: int]) ->
    implies (0 <= u && u < n) (select h u == mk_put (u, u) ())
     : [%v: unit])
    : [%h: tr])
    [@under]

let[@rty] ctx =
  let[@sigma] n = ((v >= 0 && len h == 0 : [%v: int]) : [%h: tr]) [@under] in
  let[@sigma] b =
    ((iff v (n <= 0) && len h == 0 : [%v: bool]) : [%h: tr]) [@under]
  in
  let[@sigma] u1 = ((len h == 0 : [%v: unit]) : [%h: tr]) [@under] in
  let[@sigma] branch1 = ((b && len h == 0 : [%v: unit]) : [%h: tr]) [@under] in
  let[@sigma] u2 =
    ((len h == 1 && select h 0 == mk_put (n, n) () : [%v: unit])
      : [%h: tr])
      [@under]
  in
  let[@sigma] m =
    ((v == n - 1 && len h == 0 : [%v: int]) : [%h: tr]) [@under]
  in
  let[@sigma] rec_res =
    ((len h == m && fun (u : [%forall: int]) ->
      implies (0 <= u && u < m) (select h u == mk_put (u, u) ())
       : [%v: unit])
      : [%h: tr])
      [@under]
  in
  let[@sigma] rec_res_close_m =
    ((fun (m_ : [%exists: int]) (mh_ : [%exists: tr]) ->
        m_ == n - 1
        && len mh_ == 0
        && len h == m_ + len mh_
        && fun (u : [%forall: int]) ->
        implies (0 <= u && u < m_) (select h u == mk_put (u, u) ())
       : [%v: unit])
      : [%h: tr])
      [@under]
  in
  let[@sigma] rec_res_close_u2 =
    ((fun (u2_ : [%exists: unit]) (u2h_ : [%exists: tr]) (m_ : [%exists: int])
          (mh_ : [%exists: tr]) ->
        len u2h_ == 1
        && select u2h_ 0 == mk_put (n, n) ()
        && m_ == n - 1
        && len mh_ == 0
        && len h == m_ + len mh_ + len u2h_
        && (fun (u : [%forall: int]) ->
             implies (0 <= u && u < m_) (select h u == mk_put (u, u) ()))
        && fun (u : [%forall: int]) ->
        implies
          (m_ <= u && u < m_ + len u2h_)
          (select h u == select u2h_ (u - m_))
       : [%v: unit])
      : [%h: tr])
      [@under]
  in
  let[@sigma] branch2 =
    ((fun (u2_ : [%exists: unit]) (u2h_ : [%exists: tr]) (m_ : [%exists: int])
          (mh_ : [%exists: tr]) ->
        (not b)
        && len u2h_ == 1
        && select u2h_ 0 == mk_put (n, n) ()
        && m_ == n - 1
        && len mh_ == 0
        && len h == m_ + len mh_ + len u2h_
        && (fun (u : [%forall: int]) ->
             implies (0 <= u && u < m_) (select h u == mk_put (u, u) ()))
        && fun (u : [%forall: int]) ->
        implies
          (m_ <= u && u < m_ + len u2h_)
          (select h u == select u2h_ (u - m_))
       : [%v: unit])
      : [%h: tr])
      [@under]
  in
  let[@sigma] merged =
    (((b && len h == 0)
      || fun (u2_ : [%exists: unit]) (u2h_ : [%exists: tr])
        (m_ : [%exists: int]) (mh_ : [%exists: tr]) ->
      (not b)
      && len u2h_ == 1
      && select u2h_ 0 == mk_put (n, n) ()
      && m_ == n - 1
      && len mh_ == 0
      && len h == m_ + len mh_ + len u2h_
      && (fun (u : [%forall: int]) ->
           implies (0 <= u && u < m_) (select h u == mk_put (u, u) ()))
      && fun (u : [%forall: int]) ->
      implies (m_ <= u && u < m_ + len u2h_) (select h u == select u2h_ (u - m_))
       : [%v: unit])
      : [%h: tr])
      [@under]
  in
  let[@sigma] merged_close_b =
    ((fun (b_ : [%exists: bool]) (bh_ : [%exists: tr]) ->
        iff b_ (n <= 0)
        && len bh_ == 0
        && ( (b && len h == 0)
           || fun (u2_ : [%exists: unit]) (u2h_ : [%exists: tr])
             (m_ : [%exists: int]) (mh_ : [%exists: tr]) ->
             (not b)
             && len u2h_ == 1
             && select u2h_ 0 == mk_put (n, n) ()
             && m_ == n - 1
             && len mh_ == 0
             && len h == m_ + len mh_ + len u2h_
             && (fun (u : [%forall: int]) ->
                  implies (0 <= u && u < m_) (select h u == mk_put (u, u) ()))
             && fun (u : [%forall: int]) ->
             implies
               (m_ <= u && u < m_ + len u2h_)
               (select h u == select u2h_ (u - m_)) )
       : [%v: unit])
      : [%h: tr])
      [@under]
  in
  ((len h == n && fun (u : [%forall: int]) ->
    implies (0 <= u && u < n) (select h u == mk_put (u, u) ())
     : [%v: unit])
    : [%h: tr])
    [@under]
