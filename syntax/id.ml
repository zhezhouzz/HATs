module type ID = sig
  type id

  val layout : id -> string
  val eq : id -> id -> bool
end

module Id = struct
  type id = string

  let layout x = x
  let eq = String.equal
end
