module T = Language.TypedTermlang
open Language.TypedCoreEff
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
  let rec aux f = function
    | [] -> f
    | arg :: args -> aux (App (f, [ arg ])) #: (get_argty f.ty) args
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
          construct_lete lhs e (to_comp @@ var_to_v lhs))
    expr

and normalize_get_values (k : vconts) (es : T.term T.typed list) : comp typed =
  (List.fold_left
     (fun (k : vconts) rhs ids ->
       normalize_get_value (fun id -> k (id :: ids)) rhs)
     k es)
    []

and normalize_handler (hd : T.handler T.typed) : handler typed =
  let T.{ ret_case = { retarg; retbody }; handler_cases } = hd.x in
  let ret_case = { retarg; retbody = normalize_term retbody } in
  let handler_cases =
    List.map
      (fun T.{ effop; effargs; effk; hbody } ->
        { effop; effargs; effk; hbody = normalize_term hbody })
      handler_cases
  in
  { ret_case; handler_cases } #: hd.ty

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
  | T.VHd hd -> k (CVal (VHd (normalize_handler hd)))
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
  | T.(Perform { rhsop; rhsargs }) ->
      normalize_get_values
        (fun appopargs -> k (CAppPerform { effop = rhsop; appopargs }))
        rhsargs
  | T.(CWithH { handler; handled_prog }) ->
      k
        (CWithH
           {
             handler = normalize_handler handler;
             handled_prog = normalize_term handled_prog;
           })
  | T.(App (func, [ arg ])) ->
      normalize_get_value
        (fun appf -> normalize_get_value (fun arg -> k' (mk_app appf arg)) arg)
        func
  | T.(App (func, args)) -> normalize_get_comp k' (decurry (func, args))
  | T.(Ite (cond, et, ef)) ->
      normalize_get_value
        (fun cond ->
          k (CIte { cond; et = normalize_term et; ef = normalize_term ef }))
        cond
  | T.(Match (matched, match_cases)) ->
      normalize_get_value
        (fun matched ->
          let match_cases =
            List.map
              (fun T.{ constructor; args; exp } ->
                { constructor; args; exp = normalize_term exp })
              match_cases
          in
          k (CMatch { matched; match_cases }))
        matched
