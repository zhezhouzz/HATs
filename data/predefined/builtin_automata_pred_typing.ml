let[@pred] storedP (k : int) (value : int) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : int) = _F (Put ((k [@d]), x_1, v, true))

let[@pred] mkdirP (p : int) =
  Put ((p [@d]), x_1, v, is_dir x_1)
  && _X (_G (not (Put ((p [@d]), x_1, v, is_deleted x_1))))
