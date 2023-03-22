module T = Language.TypedTermlang
open Language.TypedCoreEff
open Sugar
open Zzdatatype.Datatype

type cont = comp typed -> comp typed
type vcont = value typed -> comp typed
type vconts = value typed list -> comp typed
type ncont = string typed -> comp typed

let new_x () = Rename.unique "x"
let construct_lete lhs rhs letbody = (CLetE { lhs; rhs; letbody }) #: letbody.ty
let var_to_v x = (VVar x.x) #: x.ty

let append_lete (k : ncont) (rhs : comp typed) =
  let lhs = (new_x ()) #: rhs.ty in
  construct_lete lhs rhs (k lhs)

let vcont_to_cont (k : value typed -> comp typed) (rhs : comp typed) :
    comp typed =
  let lhs = (new_x ()) #: rhs.ty in
  construct_lete lhs rhs (k (var_to_v lhs))

let rec normalize_term (tm : T.term T.typed) : comp typed =
  normalize_cont_ (fun x -> x) tm

and normalize_ncont_ (k : ncont) (e : T.term T.typed) : comp typed =
  normalize_vcont_
    (fun v ->
      match v.x with
      | VVar name -> k name #: v.ty
      | _ -> append_lete k (to_comp v))
    e

and normalize_vcont_ (k : vcont) (expr : T.term T.typed) : comp typed =
  normalize_cont_
    (fun e ->
      match e.x with
      | CVal v -> k v #: e.ty
      | _ -> _failatwith __FILE__ __LINE__ "bad")
    expr

and normalize_vconts_ (k : vconts) (es : T.term T.typed list) : comp typed =
  (List.fold_left
     (fun (k : vconts) rhs ids ->
       normalize_vcont_ (fun id -> k (id :: ids)) rhs)
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

and mk_application (k : cont) (rhsf : value typed) (rhsarg : value typed) =
  let res_ty = get_retty rhsf.ty in
  let lhs = (new_x ()) #: res_ty in
  ( (fun letbody -> k (CLetApp { lhs; rhsf; rhsarg; letbody }) #: letbody.ty),
    var_to_v lhs )

and normalize_cont_ (k : cont) (expr : T.term T.typed) : comp typed =
  let rec aux (k' : cont) expr =
    let k e = k e #: expr.ty in
    match expr.x with
    | T.Err -> k CErr
    | T.Tu _ -> _failatwith __FILE__ __LINE__ "unimp"
    | T.Var var -> k (CVal (VVar var))
    | T.Const c ->
        k (CVal (VConst c)) (* NOTE: do we need a name of a function? *)
    | T.Lam { lamarg; lambody } ->
        k (CVal (VLam { lamarg; lambody = normalize_term lambody }))
    | T.VHd hd -> k (CVal (VHd (normalize_handler hd)))
    | T.(Let { if_rec; lhs; rhs; letbody }) -> (
        if if_rec then _failatwith __FILE__ __LINE__ "unimp"
        else
          match lhs with
          | [] -> _failatwith __FILE__ __LINE__ "bad"
          | [ lhs ] ->
              aux (fun rhs -> construct_lete lhs rhs (aux k' letbody)) rhs
          | _ -> _failatwith __FILE__ __LINE__ "unimp")
    | T.(AppOp _) -> _failatwith __FILE__ __LINE__ "unimp"
    | T.(Perform { rhsop; rhsargs }) ->
        normalize_vconts_
          (fun rhsargs ->
            let lhs = (new_x ()) #: expr.ty in
            (CLetPerform
               {
                 lhs;
                 rhsop;
                 rhsargs;
                 letbody = xmap (fun x -> CVal (VVar x)) lhs;
               })
            #: expr.ty)
          rhsargs
    | T.(CWithH { handler; handled_prog }) ->
        k
          (CWithH
             {
               handler = normalize_handler handler;
               handled_prog = normalize_term handled_prog;
             })
    | T.(App (func, args)) ->
        normalize_vcont_
          (fun rhsf ->
            normalize_vconts_
              (fun rhsargs ->
                if List.length rhsargs == 0 then
                  _failatwith __FILE__ __LINE__ "bad"
                else
                  let k', v =
                    List.fold_left
                      (fun (k, rhsf) rhsarg -> mk_application k rhsf rhsarg)
                      ((fun x -> x), rhsf)
                      rhsargs
                  in
                  k' (k (CVal v.x)))
              args)
          func
    | T.(Ite _) -> _failatwith __FILE__ __LINE__ "unimp"
    | T.(Match _) -> _failatwith __FILE__ __LINE__ "unimp"
  in
  aux k expr
