let[@pred] rI (s1 : Node.t) (s2 : Node.t) (c : Color.t) =
  (* _G (implies (existsEP s1 s2) (existsCP s1 && existsCP s2)) *)
  (* && _G (not (existsEP s1 s2 && storedCP s1 c && storedCP s2 c)) *)
  implies (existsEP s1 s2) (existsCP s1 && existsCP s2)
  && not (existsEP s1 s2 && storedCP s1 c && storedCP s2 c)
