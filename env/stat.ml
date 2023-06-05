type stat = {
  is_rec : bool;
  code_size : int;
  code_branchs : int;
  code_effects : int;
  code_lits : int;
  smt_query_time_record : float list;
  inclusion_query_time_record : float list;
  max_inclusion_alphabet : int;
  max_inclusion_automaton_size : int;
}

let init (is_rec, code_size, code_branchs, code_effects) =
  {
    is_rec;
    code_size;
    code_branchs;
    code_effects;
    code_lits = 0;
    smt_query_time_record = [];
    inclusion_query_time_record = [];
    max_inclusion_alphabet = 0;
    max_inclusion_automaton_size = 0;
  }

let update_dynamic_stat stat
    ( smt_query_time_record,
      inclusion_query_time_record,
      max_inclusion_alphabet,
      max_inclusion_automaton_size ) code_lits =
  {
    stat with
    code_lits;
    smt_query_time_record;
    inclusion_query_time_record;
    max_inclusion_alphabet;
    max_inclusion_automaton_size;
  }

let dump_one stat =
  `Assoc
    [
      ("is_rec", `Bool stat.is_rec);
      ("code_size", `Int stat.code_size);
      ("code_branchs", `Int stat.code_branchs);
      ("code_effects", `Int stat.code_effects);
      ("code_lits", `Int stat.code_lits);
      ( "smt_query_time_record",
        `List (List.map (fun x -> `Float x) stat.smt_query_time_record) );
      ( "inclusion_query_time_record",
        `List (List.map (fun x -> `Float x) stat.inclusion_query_time_record) );
      ("max_inclusion_alphabet", `Int stat.max_inclusion_alphabet);
      ("max_inclusion_automaton_size", `Int stat.max_inclusion_automaton_size);
    ]

let dump filename stats =
  let j =
    `List
      (List.map
         (fun (idx, if_well_typed, stat) ->
           `Assoc
             [
               ("idx", `Int idx);
               ("stat", dump_one stat);
               ("if_well_typed", `Bool if_well_typed);
             ])
         stats)
  in
  let oc = Core.Out_channel.create filename in
  Yojson.Basic.to_channel oc j;
  Core.Out_channel.close oc
