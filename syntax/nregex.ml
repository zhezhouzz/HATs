module T = struct
  open Sexplib.Std
  open Zzdatatype.Datatype

  type mt = { op : string; gobal_embedding : int; local_embedding : int }
  [@@deriving sexp]

  type mts = int list StrMap.t IntMap.t

  let fold_mts f i_s_i res =
    IntMap.fold
      (fun gobal_embedding s_i res ->
        StrMap.fold
          (fun op local_embedding res ->
            f { gobal_embedding; op; local_embedding } res)
          s_i res)
      i_s_i res

  let rec pow a = function
    | 0 -> 1
    | 1 -> a
    | n ->
        let b = pow a (n / 2) in
        b * b * if n mod 2 = 0 then 1 else a

  let rec id_to_bl len n res =
    if len == 0 then res
    else
      let x = 0 == n mod 2 in
      id_to_bl (len - 1) (n / 2) (x :: res)

  let id_to_barr len n = Array.of_list @@ id_to_bl len n []

  type reg =
    | Epslion
    | Minterm of mt
    | Union of reg list
    | Concat of reg list
    | Star of reg
  [@@deriving sexp]
end
