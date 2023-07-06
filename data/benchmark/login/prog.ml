type effect =
  | Put of (int -> int -> int -> unit)
  | Get of (int -> int -> int)
  | Mem of (int -> int -> bool)
  | Other of (unit -> unit)

(* let[@assert] f1 ?l:(lo = (true : [%v: unit]) [@over]) = *)
(*   { *)
(*     pre = starA anyA; *)
(*     post = *)
(*       ((starA (Other ((true : [%v0: unit]) : [%v1: unit])); *)
(*         Ret (is_none v0 : [%v0: int])) : int); *)
(*   } *)

(* let[@assert] f2 ?l:(lo = (true : [%v: unit]) [@over]) = *)
(*   { *)
(*     pre = starA anyA; *)
(*     post = *)
(*       ((starA (Other ((true : [%v0: unit]) : [%v1: unit])); *)
(*         Ret (is_none v0 : [%v0: int])) : int); *)
(*   } *)

(* let[@assert] f3 ?l:(lo = (true : [%v: unit]) [@over]) = *)
(*   { *)
(*     pre = starA anyA; *)
(*     post = *)
(*       ((starA (Other ((true : [%v0: unit]) : [%v1: unit])); *)
(*         Ret (is_none v0 : [%v0: int])) : int); *)
(*   } *)

let rec prog auth_tab pw_tab data_tab (id : int) (pw : int) : int =
  if perform (Mem (auth_tab, id)) then
    let (auth_res : int) = perform (Get (auth_tab, id)) in
    if auth_res == 0 then -1
    else
      let (pw2 : int) = perform (Get (pw_tab, id)) in
      if pw != stored_pw then
        let (dummy0 : unit) = perform (Put (auth_tab, 0)) in
        -1
      else perform (Get (data_tab, id))
  else -1
