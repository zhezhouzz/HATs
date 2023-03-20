external method_predicates : t = "len" "<="
(* 
let[@library] int_gen =
  let (dummy : [%over: unit]) = (true : [%v: unit]) in
  (true : [%v: int])

let[@library] sizecheck =
  let (x : [%over: int]) = (true : [%v: int]) in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool])

let[@library] subs =
    let (s : [%over: int]) = (true : [%v: int]) in
    (v == (s - 1) : [%v: int])

let[@library] bool_gen =
  let (dummy : [%over: unit]) = (true : [%v: unit]) in
  (true : [%v: bool]) *)

let[@library] s01 = 
   (true : [%v: int]) [@under]

let[@library] s = 
   (true : [%v: int]) [@under]  

   
let goal =
  let size = (0 <= v : [%v: int]) [@over] in
  (fun (u : [%forall: int]) -> implies (len v u) (0 <= u && u <= size)
    : [%v: int tree])
    [@under]
