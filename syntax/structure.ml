module F (L : Lit.T) = struct
  include Termlang.F (L)
  module R = Rty.F (L)
  module LR = R.LRty

  type rty_kind = RtyLib | RtyToCheck

  type entry =
    | SrlPred of {
        name : string;
        args : string Normalty.Ntyped.typed list;
        srl_body : R.regex;
      }
    | LtlfPred of {
        name : string;
        args : string Normalty.Ntyped.typed list;
        ltlf_body : R.LTLf.ltlf;
      }
    | Type_dec of Type_dec.t
    | Func_dec of string Normalty.Ntyped.typed
    | FuncImp of { name : string; if_rec : bool; body : term typed }
    | Rty of { name : string; kind : rty_kind; rty : R.rty }
    | LtlfRty of { name : string; kind : rty_kind; rty : LR.rty }

  type structure = entry list

  (* open Sugar *)
  open Zzdatatype.Datatype

  let inline_ltlf_pred_one pred entry =
    match entry with
    | LtlfPred { name; args; ltlf_body } ->
        (* let () = *)
        (*   if String.equal name name' then _failatwith __FILE__ __LINE__ "die" *)
        (*   else () *)
        (* in *)
        let ltlf_body = R.LTLf.apply_pred pred ltlf_body in
        LtlfPred { name; args; ltlf_body }
    | LtlfRty { name; kind; rty } ->
        LtlfRty { name; kind; rty = R.apply_pred_rty pred rty }
    | _ -> entry

  let inline_ltlf_pred entrys =
    let rec aux res entrys =
      match entrys with
      | [] -> res
      | LtlfPred { name; args; ltlf_body } :: entrys ->
          let entrys =
            List.map (inline_ltlf_pred_one (name, args, ltlf_body)) entrys
          in
          aux res entrys
      | entry :: entrys -> aux (res @ [ entry ]) entrys
    in
    aux [] entrys

  let ltlf_to_srl_ entry =
    match entry with
    | LtlfPred { name; args; ltlf_body } ->
        SrlPred
          {
            name;
            args;
            srl_body = R.SRL.normalize_name @@ R.LTLf.to_srl ltlf_body;
          }
    | LtlfRty { name; kind; rty } ->
        Rty { name; kind; rty = R.normalize_name_rty @@ R.to_rty rty }
    | _ -> entry

  let ltlf_to_srl = List.map ltlf_to_srl_

  let mk_normal_top_ctx_ = function
    | Rty { name; kind; rty } -> (
        match kind with
        | RtyLib -> [ (name, R.erase_rty rty) ]
        | RtyToCheck -> [])
    | LtlfRty { name; kind; rty } -> (
        match kind with
        | RtyLib -> [ (name, LR.erase_rty rty) ]
        | RtyToCheck -> [])
    | Func_dec x -> [ (x.x, x.ty) ]
    | FuncImp _ | Type_dec _ | LtlfPred _ | SrlPred _ -> []

  let mk_normal_top_opctx_ = function
    | Type_dec d ->
        List.map (fun R.Nt.{ x; ty } -> (x, ty)) @@ Type_dec.mk_ctx_ d
    | _ -> []

  let mk_normal_top_ctx es = List.concat @@ List.map mk_normal_top_ctx_ es
  let mk_normal_top_opctx es = List.concat @@ List.map mk_normal_top_opctx_ es

  let map_imps f codes =
    List.map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } ->
            FuncImp { name; if_rec; body = f name if_rec body }
        | _ -> code)
      codes

  let map_rtys f codes =
    List.map
      (fun code ->
        match code with
        | Rty { name; kind; rty } -> Rty { name; kind; rty = f rty }
        | _ -> code)
      codes

  let filter_map_imps f codes =
    List.filter_map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } -> f name if_rec body
        | _ -> None)
      codes
end
