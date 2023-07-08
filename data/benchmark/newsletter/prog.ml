type effect =
  | Write of (int -> unit)
  | Read of (unit -> int)
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* table (user, news) -> [v <= 0: unsubscribed ; v > 0: subscribed] *)
(* code_bound n: less than n is valid *)

(* let unsubscribe (user : nat) (news : int) : int = *)
(*   if perform (Mem (user, news)) then *)
(*     let (last_code : int) = perform (Read ()) in *)
(*     let (new_code : int) = last_code + 1 in *)
(*     let (dummy0 : unit) = perform (Write new_code) in *)
(*     let (dummy1 : unit) = perform (Update (user, news, new_code)) in *)
(*     () *)
(*   else -1 *)

let rec multi_confirm (user : nat) (news_lo : int) (news_hi : int) (code : int)
    : unit =
  if news_lo == news_hi then ()
  else
    let (last_code : int) = perform (Read ()) in
    if code == last_code then
      let (new_code : int) = last_code + 1 in
      let (dummy0 : unit) = perform (Write new_code) in
      if perform (Mem (user, news_lo)) then
        let (is_subc : int) = perform (Lookup (user, news_lo)) in
        if is_subc <= 0 then
          let (dummy1 : unit) = perform (Update (user, news_lo, 1)) in
          let (dummy2 : unit) = perform (Update (user, news_lo + 1, -1)) in
          let (dummy3 : unit) =
            multi_confirm user (news_lo + 1) news_hi new_code
          in
          ()
        else ()
      else ()
    else ()

let[@assert] multi_confirm ?l:(user = (true : [%v: nat]))
    ?l:(news_lo = (true : [%v: int])) ?l:(news_hi = (news_lo <= v : [%v: int]))
    ?l:(code = (0 < v : [%v: int])) =
  {
    pre =
      (starA anyA;
       Write ((v0 == code : [%v0: int]) : [%v: unit]);
       starA (anyA - Write ((true : [%v0: int]) : [%v: unit]));
       Update
         ((((v0 == user && v1 == news_lo && v2 <= 0 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Write ((true : [%v0: int]) : [%v: unit])
         - Update
             ((((v0 == user && v1 == news_lo : [%v0: nat]) : [%v1: int])
                : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Write ((true : [%v0: int]) : [%v: unit])
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]))
        || starA
             (starA
                (anyA
                - Write ((true : [%v0: int]) : [%v: unit])
                - Update
                    ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int])
                      : [%v: unit]));
              Write ((v0 == 1 + code : [%v0: int]) : [%v: unit]);
              starA
                (anyA
                - Write ((true : [%v0: int]) : [%v: unit])
                - Update
                    ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int])
                      : [%v: unit]));
              Update
                ((((v0 == user && v1 == news_lo && v2 > 0 : [%v0: nat])
                    : [%v1: int])
                   : [%v2: int])
                  : [%v: unit]);
              Update
                ((((v0 == user && v1 == news_lo + 1 && v2 <= 0 : [%v0: nat])
                    : [%v1: int])
                   : [%v2: int])
                  : [%v: unit]);
              starA
                (anyA
                - Update
                    ((((v0 == user && v1 <= news_lo : [%v0: nat]) : [%v1: int])
                       : [%v2: int])
                      : [%v: unit])));
        Ret (true : [%v0: unit])) : unit);
  }

(* (anyA *)
(* - Write ((true : [%v0: int]) : [%v: unit]) *)
(* - Update *)
(*     ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit])) *)

(* let confirm (user : nat) (news : int) (code : int) : unit = *)
(*   let (last_code : int) = perform (Read ()) in *)
(*   if code <= last_code then *)
(*     if perform (Mem (user, news)) then *)
(*       let (is_subc : int) = perform (Lookup (user, news)) in *)
(*       if is_subc > 0 then *)
(*         let (dummy1 : unit) = perform (Update (user, news, -1)) in *)
(*         () *)
(*       else () *)
(*     else () *)
(*   else () *)

(* let[@assert] confirm ?l:(user = (true : [%v: nat])) *)
(*     ?l:(news = (true : [%v: int])) ?l:(code = (0 <= v : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Write ((v0 >= code : [%v0: int]) : [%v: unit]); *)
(*        starA (anyA - Write ((true : [%v0: int]) : [%v: unit])); *)
(*        Update *)
(*          ((((v0 == user && v1 == news && v2 > 0 : [%v0: nat]) : [%v1: int]) *)
(*             : [%v2: int]) *)
(*            : [%v: unit]); *)
(*        starA *)
(*          (anyA *)
(*          - Write ((true : [%v0: int]) : [%v: unit]) *)
(*          - Update *)
(*              ((((v0 == user && v1 == news : [%v0: nat]) : [%v1: int]) *)
(*                 : [%v2: int]) *)
(*                : [%v: unit]))); *)
(*     post = *)
(*       ((starA *)
(*           (anyA *)
(*           - Write ((true : [%v0: int]) : [%v: unit]) *)
(*           - Update *)
(*               ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit])); *)
(*         Update *)
(*           ((((v0 == user && v1 == news && not (v2 > 0) : [%v0: nat]) *)
(*               : [%v1: int]) *)
(*              : [%v2: int]) *)
(*             : [%v: unit]); *)
(*         Ret (true : [%v0: unit])) : unit); *)
(*   } *)
