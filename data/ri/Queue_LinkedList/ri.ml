let[@pred] rI =
  (* _G (implies (SetNext ((c [@d]), x_1, v, true)) (is_storedP c)) *)
  (* && _G (implies (SetNext (x_0, (c [@d]), v, true)) (is_storedP c)) *)
  (* && *)
  _G (not (SetNext (x_0, x_1, v, x_0 == x_1)))
