let[@pred] rI (s : Node.t) =
  (not (is_node s)) || has_connect_in s || has_connect_out s
