open Language
module T = Structure
open TypedCoreEff
open Sugar
open Zzdatatype.Datatype

type cont = comp typed -> comp typed
type vcont = value typed -> comp typed
type vconts = value typed list -> comp typed

let new_x () = Rename.unique "x"
let construct_lete lhs rhs letbody = (CLetE { lhs; rhs; letbody }) #: letbody.ty
let var_to_v x = (VVar x.x) #: x.ty

let vcont_to_cont (k : value typed -> comp typed) (rhs : comp typed) :
    comp typed =
  let lhs = (new_x ()) #: rhs.ty in
  construct_lete lhs rhs (k (var_to_v lhs))

let decurry (f, args) =
  let open T in
  (* let () = *)
  (*   Printf.printf "decurry: %s   %s\n" (T.layout f) *)
  (*     (List.split_by_comma T.layout args) *)
  (* in *)
  let rec aux f = function
    | [] -> f
    | arg :: args -> aux (App (f, [ arg ])) #: (get_retty f.ty) args
  in
  aux f args

let rec normalize_term (tm : T.term T.typed) : comp typed =
  normalize_get_comp (fun x -> x) tm

and normalize_get_value (k : vcont) (expr : T.term T.typed) : comp typed =
  normalize_get_comp
    (fun e ->
      match e.x with
      | CVal v -> k v #: e.ty
      | _ ->
          let lhs = (new_x ()) #: e.ty in
          construct_lete lhs e (k @@ var_to_v lhs))
    expr

and normalize_get_values (k : vconts) (es : T.term T.typed list) : comp typed =
  (List.fold_left
     (fun (k : vconts) rhs ids ->
       normalize_get_value (fun id -> k (id :: ids)) rhs)
     k es)
    []

and normalize_get_comp (k' : cont) (expr : T.term T.typed) : comp typed =
  let k e = k' e #: expr.ty in
  match expr.x with
  | T.Err -> k CErr
  | T.Tu es -> normalize_get_values (fun vs -> k (CVal (VTu vs))) es
  | T.Var var -> k (CVal (VVar var))
  | T.Const c ->
      k (CVal (VConst c)) (* NOTE: do we need a name of a function? *)
  | T.Lam { lamarg; lambody } ->
      k (CVal (VLam { lamarg; lambody = normalize_term lambody }))
  | T.(Let { if_rec; lhs; rhs; letbody }) -> (
      match (if_rec, lhs) with
      | true, fixname :: fixarg :: args ->
          normalize_get_comp
            (fun rhs ->
              let fixbody =
                List.fold_left
                  (fun e lamarg -> to_comp (mk_lam lamarg e))
                  rhs args
              in
              let rhs = to_comp @@ mk_fix fixname fixarg fixbody in
              construct_lete fixname rhs (normalize_get_comp k' letbody))
            rhs
      | true, _ -> _failatwith __FILE__ __LINE__ "bad"
      | false, [] -> _failatwith __FILE__ __LINE__ "bad"
      | false, [ lhs ] ->
          normalize_get_comp
            (fun rhs -> construct_lete lhs rhs (normalize_get_comp k' letbody))
            rhs
      | false, tulhs ->
          normalize_get_value
            (fun rhs ->
              let letbody = normalize_get_comp k' letbody in
              (CLetDeTu { tulhs; turhs = rhs; letbody }) #: letbody.ty)
            rhs)
  | T.(AppOp (op, es)) ->
      normalize_get_values (fun appopargs -> k (CAppOp { op; appopargs })) es
  | T.(App (func, [ arg ])) ->
      normalize_get_value
        (fun appf -> normalize_get_value (fun arg -> k' (mk_app appf arg)) arg)
        func
  | T.(App (func, args)) -> normalize_get_comp k' (decurry (func, args))
  | T.(Ite (cond, et, ef)) ->
      normalize_get_comp k'
        T.(
          (Match
             ( cond,
               [
                 { constructor = "True" #: bool_ty; args = []; exp = et };
                 { constructor = "False" #: bool_ty; args = []; exp = ef };
               ] ))
          #: expr.ty)
  (* | T.(Ite (cond, et, ef)) -> *)
  (*     normalize_get_value *)
  (*       (fun cond -> *)
  (*         k (CIte { cond; et = normalize_term et; ef = normalize_term ef })) *)
  (*       cond *)
  | T.(Match (matched, match_cases)) ->
      normalize_get_value
        (fun matched ->
          let match_cases =
            List.map
              (fun T.{ constructor; args; exp } ->
                { constructor; args; exp = normalize_get_comp k' exp })
              match_cases
          in
          (CMatch { matched; match_cases }) #: expr.ty)
        matched

module S = Language.Structure

let get_normalized_code code =
  S.filter_map_imps
    (fun name if_rec body ->
      let body = normalize_term body in
      let e = if if_rec then lam_to_fix_comp name #: body.ty body else body in
      Some (name, e))
    code
