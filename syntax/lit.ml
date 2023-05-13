module type T = sig
  include Typed.T

  type lit =
    | AC of Constant.t
    | AVar of string
    | ATu of lit typed list
    | AProj of lit typed * int
    | AAppOp of Op.t typed * lit typed list
  [@@deriving sexp]

  val mk_lit_true : lit
  val mk_lit_false : lit
  val subst_lit : string * lit -> lit -> lit
  val fv_lit : lit -> string list
  val fv_typed_lit : lit typed -> string list
  val fv_typed_lits : lit typed list -> string list
  val get_eqlit_by_name : lit -> string -> lit option
  val compare : lit -> lit -> int
  val eq_lit : lit -> lit -> bool
  val mk_int_l1_eq_l2 : lit -> lit -> lit
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std
  module T = Ty
  include Ty

  type lit =
    | AC of Constant.t
    | AVar of string
    | ATu of lit typed list
    | AProj of lit typed * int
    | AAppOp of Op.t typed * lit typed list
  [@@deriving sexp]

  let compare l1 l2 = Sexplib.Sexp.compare (sexp_of_lit l1) (sexp_of_lit l2)
  let eq_lit l1 l2 = 0 == compare l1 l2
  let mk_lit_true = AC (Constant.B true)
  let mk_lit_false = AC (Constant.B false)
  let get_var_opt = function AVar x -> Some x | _ -> None

  let mk_int_l1_eq_l2 l1 l2 =
    let mk_eq_typed_op =
      Op.mk_eq_op #: T.(mk_arr (mk_arr int_ty int_ty) int_ty)
    in
    AAppOp (mk_eq_typed_op, [ l1 #: T.int_ty; l2 #: T.int_ty ])

  let get_subst_pair a b =
    match get_var_opt a with Some a -> [ (a, b) ] | None -> []

  let get_eqlits lit =
    match lit with
    | AAppOp (op, [ a; b ]) when Op.id_eq_op op.x ->
        get_subst_pair a.x b.x @ get_subst_pair b.x a.x
    | _ -> []

  open Sugar

  let get_eqlit_by_name lit x =
    let res =
      List.filter_map
        (fun (y, z) -> if String.equal x y then Some z else None)
        (get_eqlits lit)
    in
    match res with
    | [] -> None
    | [ z ] -> Some z
    | [ _; z ] -> Some z
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let subst_lit (y, lit) e =
    let rec aux e =
      match e with
      | AC _ -> e
      | AVar x -> if String.equal x y then lit else e
      | ATu ls -> ATu (List.map (fun x -> aux #-> x) ls)
      | AProj (l, idx) -> AProj (aux #-> l, idx)
      | AAppOp (op, ls) -> AAppOp (op, List.map (fun x -> aux #-> x) ls)
    in
    aux e

  let rec fv_lit (e : lit) =
    let aux e =
      match e with
      | AC _ -> []
      | AVar x -> [ x ]
      | ATu ls -> fv_typed_lits ls
      | AProj (l, _) -> fv_typed_lit l
      | AAppOp (_, ls) -> fv_typed_lits ls
    in
    aux e

  and fv_typed_lit e = fv_lit e.x
  and fv_typed_lits ls = List.concat @@ List.map fv_typed_lit ls
end

module Ty = struct
  include Normalty.Ntyped
end

module OptTy = struct
  include Normalty.NOpttyped
end

module LitRaw = F (OptTy)
module Lit = F (Ty)
