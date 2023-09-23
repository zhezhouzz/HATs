open Z3
open Z3.Expr
open Z3.Boolean
open Z3.Arithmetic
open Normalty.Ntyped
module T = Normalty.SMTtyped
open Sugar

let find_const_in_model m x =
  let cs = Z3.Model.get_const_decls m in
  let i =
    List.find_opt
      (fun d ->
        let name = Z3.Symbol.to_string @@ Z3.FuncDecl.get_name d in
        (* let () = Printf.printf "Find (%s) in %s\n" x name in *)
        String.equal name x)
      cs
  in
  match i with
  | Some i ->
      (* let () = Printf.printf "Const %s\n" @@ Z3.FuncDecl.to_string i in *)
      Some (Z3.FuncDecl.apply i [])
  | None -> None

let get_int_by_name m x =
  let i = find_const_in_model m x in
  match i with
  | None -> None
  | Some i -> (
      match Z3.Model.eval m i false with
      (* match Z3.Model.get_const_interp m i with *)
      | None -> _failatwith __FILE__ __LINE__ "get_int"
      | Some v ->
          (* Printf.printf "get_int(%s)\n" (Z3.Expr.to_string v); *)
          Some (int_of_string @@ Z3.Arithmetic.Integer.numeral_to_string v))

let get_string_by_name m x =
  let i = find_const_in_model m x in
  match i with
  | None -> None
  | Some i -> (
      match Z3.Model.eval m i false with
      (* match Z3.Model.get_const_interp m i with *)
      | None -> _failatwith __FILE__ __LINE__ "get_string"
      | Some v ->
          let str = Expr.to_string v in
          let str = List.of_seq @@ String.to_seq str in
          let str = List.filter (fun c -> not (Char.equal c '"')) str in
          let str = String.of_seq @@ List.to_seq str in
          (* Printf.printf "get_int(%s)\n" (Z3.Expr.to_string v); *)
          Some str)

let int_to_z3 ctx i = mk_numeral_int ctx i (Integer.mk_sort ctx)
let bool_to_z3 ctx b = if b then mk_true ctx else mk_false ctx

let tp_to_sort ctx t =
  (* let () = *)
  (*   Printf.printf "z3aux t: %s\n" @@ Sexplib.Sexp.to_string @@ sexp_of_t t *)
  (* in *)
  T.(
    match to_smtty t with
    | Int | Dt -> Integer.mk_sort ctx
    | Bool -> Boolean.mk_sort ctx)

let z3func ctx funcname inptps outtp =
  (* let () = Printf.printf "[%s]funcname: %s\n" __FILE__ funcname in *)
  FuncDecl.mk_func_decl ctx
    (Symbol.mk_string ctx funcname)
    (List.map (tp_to_sort ctx) inptps)
    (tp_to_sort ctx outtp)

(* let arrname_arr arrname = arrname ^ "_a" *)
(* let arrname_length arrname = arrname ^ "_length" *)

(* let arrii_to_z3 ctx name = *)
(*   Z3Array.mk_const_s ctx (arrname_arr name) (Integer.mk_sort ctx) *)
(*     (Integer.mk_sort ctx) *)

(* let array_head_ ctx (arrname, idx) = *)
(*   let a_length = Integer.mk_const_s ctx (arrname_length arrname) in *)
(*   [ mk_lt ctx idx a_length; mk_le ctx (int_to_z3 ctx 0) idx ] *)

(* let array_head ctx (arrname, idxname) = *)
(*   let idx = Integer.mk_const_s ctx idxname in *)
(*   array_head_ ctx (arrname, idx) *)

let tpedvar_to_z3 ctx (tp, name) =
  T.(
    match to_smtty tp with
    | Dt | Int -> Integer.mk_const_s ctx name
    | Bool -> Boolean.mk_const_s ctx name)

let make_forall ctx qv body =
  if List.length qv == 0 then body
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall_const ctx qv body (Some 1) [] [] None None)

let make_exists ctx qv body =
  if List.length qv == 0 then body
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_exists_const ctx qv body (Some 1) [] [] None None)

let z3expr_to_bool v =
  match Boolean.get_bool_value v with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> failwith "z3expr_to_bool"

(* type imp_version = V1 | V2 *)

(* let layout_imp_version = function V1 -> "V1" | V2 -> "V2" *)

(* open Zzdatatype.Datatype *)

(* let bound = 4 *)

(* let get_preds_interp model impv = *)
(*   match impv with *)
(*   | V1 -> List.init bound (fun x -> x) *)
(*   | V2 -> ( *)
(*       let funcs = Model.get_func_decls model in *)
(*       let get func = *)
(*         match Model.get_func_interp model func with *)
(*         | None -> raise @@ failwith "never happen" *)
(*         | Some interp -> *)
(*             let bounds = *)
(*               List.fold_left *)
(*                 (fun l e -> *)
(*                   Model.FuncInterp.FuncEntry.( *)
(*                     List.map *)
(*                       (fun bound -> *)
(*                         if Arithmetic.is_int_numeral bound then *)
(*                           int_of_string *)
(*                           @@ Arithmetic.Integer.numeral_to_string bound *)
(*                         else raise @@ failwith "bad bound") *)
(*                       (get_args e)) *)
(*                   @ l) *)
(*                 [] *)
(*                 (Model.FuncInterp.get_entries interp) *)
(*             in *)
(*             let bounds = List.remove_duplicates bounds in *)
(*             (\* let _ = printf "%s\n" (IntList.to_string bounds) in *\) *)
(*             bounds *)
(*       in *)
(*       let bounds = *)
(*         List.remove_duplicates @@ List.flatten @@ List.map get funcs *)
(*       in *)
(*       match IntList.max_opt bounds with *)
(*       | None -> [ 0 ] *)
(*       | Some ma -> (ma + 1) :: bounds) *)

(* let neg_avoid_timeout_constraint ctx vars body = *)
(*   if List.length vars == 0 then body *)
(*   else *)
(*     let vars = List.map (tpedvar_to_z3 ctx) vars in *)
(*     let is = List.init bound (fun i -> Arithmetic.Integer.mk_numeral_i ctx i) in *)
(*     let ps = *)
(*       List.map *)
(*         (fun x -> *)
(*           Boolean.mk_or ctx (List.map (fun i -> Boolean.mk_eq ctx x i) is)) *)
(*         vars *)
(*     in *)
(*     Boolean.mk_and ctx [ Boolean.mk_and ctx ps; body ] *)

(* let avoid_timeout_constraint ctx fv body = *)
(*   let is = List.init bound (fun i -> Arithmetic.Integer.mk_numeral_i ctx i) in *)
(*   let ps = *)
(*     List.map *)
(*       (fun x -> *)
(*         Boolean.mk_or ctx (List.map (fun i -> Boolean.mk_eq ctx x i) is)) *)
(*       fv *)
(*   in *)
(*   Boolean.mk_implies ctx (Boolean.mk_and ctx ps) body *)

(* let make_forall ctx forallvars body impv = *)
(*   let body = *)
(*     match impv with *)
(*     | V1 -> avoid_timeout_constraint ctx forallvars body *)
(*     | V2 -> body *)
(*   in *)
(*   if List.length forallvars == 0 then body *)
(*   else *)
(*     Quantifier.expr_of_quantifier *)
(*       (Quantifier.mk_forall_const ctx forallvars body (Some 1) [] [] None None) *)

(* let make_exists ctx forallvars body = *)
(*   if List.length forallvars == 0 then body *)
(*   else *)
(*     Quantifier.expr_of_quantifier *)
(*       (Quantifier.mk_exists_const ctx forallvars body (Some 1) [] [] None None) *)

(* let quanti_head ctx forallvars existsvars body = *)
(*   let p = *)
(*     if List.length existsvars == 0 then body *)
(*     else *)
(*       Quantifier.expr_of_quantifier *)
(*         (Quantifier.mk_exists_const ctx existsvars body (Some 1) [] [] None None) *)
(*   in *)
(*   if List.length forallvars == 0 then p *)
(*   else *)
(*     Quantifier.expr_of_quantifier *)
(*       (Quantifier.mk_forall_const ctx forallvars p (Some 1) [] [] None None) *)

(* let encode_ds_var ctx sort_name var_name = *)
(*   let sort = Sort.mk_uninterpreted ctx (Symbol.mk_string ctx sort_name) in *)
(*   let value_func_name = Symbol.mk_string ctx (sort_name ^ "_value") in *)
(*   let value_func = *)
(*     FuncDecl.mk_func_decl ctx value_func_name *)
(*       [ Z3.Arithmetic.Integer.mk_sort ctx ] *)
(*       sort *)
(*   in *)
(*   let index = Integer.mk_const_s ctx var_name in *)
(*   Z3.FuncDecl.apply value_func [ index ] *)
