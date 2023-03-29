val ( <= ) : int -> int -> bool
val ( - ) : int -> int -> int
val set_empty : (int * int) set
val set_insert : (int * int) set -> int * int -> (int * int) set
val set_mem : (int * int) set -> int * int -> bool
val mk_put : eff:int * int -> eff:unit -> unit
val mk_get : eff:int -> eff:int -> unit
val check_in : eff:int * int -> bool

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (_ : unit) = perform (mk_put (n, n) ()) in
    prog (n - 1)

let handler (prog : unit -> unit) =
  (match_with (prog ())
     ({
        retc = (fun (tt : unit) (s : (int * int) set) -> s);
        mk_put =
          (fun (k : unit -> (int * int) set -> (int * int) set)
               (input : int * int) (output : unit) (s : (int * int) set) ->
            let (s' : (int * int) set) = set_insert s input in
            k () s');
        mk_get =
          (fun (k : unit -> (int * int) set -> (int * int) set) (input : int)
               (output : int) ->
            k ());
        check_in =
          (fun (k : bool -> (int * int) set -> (int * int) set)
               (input : int * int) (s : (int * int) set) ->
            let (b : bool) = set_mem s input in
            k b s);
      }
       : hd:unit -> (int * int) set -> (int * int) set))
    set_empty
