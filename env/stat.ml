type elrond_stat = { num_lit : int; num_fv : int; num_pos : int; num_neg : int }

type stat = {
  is_rec : bool;
  code_size : int;
  code_branchs : int;
  code_effects : int;
  rty_lits : int;
  rty_events : int;
  smt_query_time_record : float list;
  elrond_stat_recod : elrond_stat list;
  inclusion_query_time_record : float list;
  pty_time_record : float list;
  am_time_record : float list;
  num_candicate_minterm_record : int list;
  filter_time_record : float list;
  typecheck_time : float;
  inclusion_alphabet_record : int list;
  inclusion_automaton_size_record : int list;
  max_inclusion_alphabet : int;
  max_inclusion_automaton_size : int;
}

let init (is_rec, code_size, code_branchs, code_effects, rty_events, rty_lits) =
  {
    is_rec;
    code_size;
    code_branchs;
    code_effects;
    rty_lits;
    rty_events;
    smt_query_time_record = [];
    elrond_stat_recod = [];
    inclusion_query_time_record = [];
    pty_time_record = [];
    am_time_record = [];
    num_candicate_minterm_record = [];
    filter_time_record = [];
    inclusion_alphabet_record = [];
    inclusion_automaton_size_record = [];
    typecheck_time = 0.0;
    max_inclusion_alphabet = 0;
    max_inclusion_automaton_size = 0;
  }

let update_dynamic_stat stat typecheck_time
    ( smt_query_time_record,
      inclusion_query_time_record,
      max_inclusion_alphabet,
      max_inclusion_automaton_size,
      inclusion_alphabet_record,
      inclusion_automaton_size_record ) (pty_time_record, am_time_record)
    (num_candicate_minterm_record, filter_time_record) =
  {
    stat with
    typecheck_time;
    smt_query_time_record;
    inclusion_query_time_record;
    pty_time_record;
    am_time_record;
    num_candicate_minterm_record;
    filter_time_record;
    inclusion_alphabet_record;
    inclusion_automaton_size_record;
    max_inclusion_alphabet;
    max_inclusion_automaton_size;
  }

let update_elrond stat elrond_stat_recod = { stat with elrond_stat_recod }

let dump_elrond stat =
  `Assoc
    [
      ("num_lit", `Int stat.num_lit);
      ("num_fv", `Int stat.num_fv);
      ("num_pos", `Int stat.num_pos);
      ("num_neg", `Int stat.num_neg);
    ]

let dump_one stat =
  `Assoc
    [
      ("is_rec", `Bool stat.is_rec);
      ("code_size", `Int stat.code_size);
      ("code_branchs", `Int stat.code_branchs);
      ("code_effects", `Int stat.code_effects);
      ("rty_events", `Int stat.rty_events);
      ("rty_lits", `Int stat.rty_lits);
      ("typecheck_time", `Float stat.typecheck_time);
      ( "pty_time_record",
        `List (List.map (fun x -> `Float x) stat.pty_time_record) );
      ( "am_time_record",
        `List (List.map (fun x -> `Float x) stat.am_time_record) );
      ( "smt_query_time_record",
        `List (List.map (fun x -> `Float x) stat.smt_query_time_record) );
      ( "num_candicate_minterm_record",
        `List (List.map (fun x -> `Int x) stat.num_candicate_minterm_record) );
      ( "filter_time_record",
        `List (List.map (fun x -> `Float x) stat.filter_time_record) );
      ("elrond_stat_recod", `List (List.map dump_elrond stat.elrond_stat_recod));
      ( "inclusion_query_time_record",
        `List (List.map (fun x -> `Float x) stat.inclusion_query_time_record) );
      ("max_inclusion_alphabet", `Int stat.max_inclusion_alphabet);
      ("max_inclusion_automaton_size", `Int stat.max_inclusion_automaton_size);
      ( "inclusion_alphabet_record",
        `List (List.map (fun x -> `Int x) stat.inclusion_alphabet_record) );
      ( "inclusion_automaton_size_record",
        `List (List.map (fun x -> `Int x) stat.inclusion_automaton_size_record)
      );
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
