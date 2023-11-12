let[@pred] storedP (k : Path.t) (value : Bytes.t) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : Path.t) = _F (Put ((k [@d]), x_1, v, true))

let[@pred] mkdirP (p : Path.t) =
  Put ((p [@d]), x_1, v, is_dir x_1)
  && _X (_G (not (Put ((p [@d]), x_1, v, not (is_dir x_1)))))
