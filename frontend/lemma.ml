module MetaEnv = Env
open Ocaml_parser
open Parsetree
module L = Ast.UT
module Ntyped = Ast.Ntyped
open Ast.Lemma
open Sugar

let undertype_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_fun (_, _, id, e) ->
        let id =
          match Pat.patten_to_typed_ids id with
          | [ id ] -> id
          | _ -> failwith "wrong format"
        in
        let ids, prop = aux e in
        (id :: ids, prop)
    | _ -> ([], Autov.prop_of_ocamlexpr expr)
  in
  let res = of_raw @@ aux expr in
  res

let pretty_layout lemma =
  (* let to_strings = List.map (fun x -> x.Languages.SMTtyped.x) in *)
  spf "%s." (Autov.pretty_layout_prop @@ to_prop lemma)

let pretty_print_with_lemma
    {
      vcl_lemmas;
      vcl_u_basics;
      vcl_u_dts;
      vcl_e_basics;
      vcl_head;
      vcl_e_dts;
      vcl_body;
    } =
  MetaEnv.show_debug_queries (fun _ ->
      let () = Pp.printf "@{<bold>With Lemmas:@}\n" in
      List.iter
        (fun p ->
          Pp.printf "@{<bold>lemmas:@} %s\n" @@ Autov.pretty_layout_prop p)
        vcl_lemmas;
      Quantified.print_qt (vcl_u_basics @ vcl_u_dts) vcl_e_basics;
      Pp.printf "\n@{<cyan>%s@} @{<bold>=>@}\n"
        (Autov.pretty_layout_prop vcl_head);
      Quantified.print_qt [] vcl_e_dts;
      Pp.printf "@{<magenta>%s@}\n" (Autov.pretty_layout_prop vcl_body))

let print_with_lemma (pres, prop) =
  MetaEnv.show_debug_queries (fun _ ->
      List.iter
        (fun pre ->
          Pp.printf "@{<bold>lemma: @} %s\n" @@ Autov.pretty_layout_prop pre)
        pres;
      Pp.printf "@{<bold>VC: @} %s\n" @@ Autov.pretty_layout_prop prop)
