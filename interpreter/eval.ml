open Utils
module type T = sig
  module C = Corelang.T
  module R = Result.T
  val value_to_repr: C.value -> R.repr
  val comp_to_res: C.comp -> R.res
end

module F (C: Corelang.T): T = struct
  module R = Result.T
  let rec value_to_repr (v: C.value): R.repr =
    match v with
    | VConst constant ->
      (match constant with
      | Unit -> BU
      | Int i -> BI i
      | Prim prim -> failwith "unimp")
    | VVar name -> failwith @@ "unbound name: %s" name
    | VLam {lamarg; lambody} -> F {farg = lamarg.x; fbody = comp_to_res lambody.x}
    | VOpApp {oparg} ->
      (match oparg.x with
      | VConst (Int i) -> BI i
      | _ -> failwith "runtime error: VOpApp")
    | VHd _ -> failwith "unimp"
  and comp_to_res: (c: C.comp): R.res = failwith "unimp"
end
