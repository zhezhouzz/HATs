let[@axiom] bytes1 ((content [@forall]) : Bytes.t) =
  implies (is_deleted content) (not (is_dir content))

let[@axiom] bytes2 ((content [@forall]) : Bytes.t) =
  implies (is_dir content) (not (is_deleted content))

(* let[@axiom] bytes3 ((content [@forall]) : int) ((path [@forall]) : int) = *)
(*   iff (is_deleted content) (is_deleted (add_child content path)) *)

(* let[@axiom] bytes4 ((content [@forall]) : int) ((path [@forall]) : int) = *)
(*   iff (is_dir content) (is_dir (add_child content path)) *)

let[@axiom] path1 ((path [@forall]) : Path.t) =
  (* iff (is_root path) (path == parent path) *)
  not (path == parent path)

let[@axiom] elem1 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies (elem_lt a b || elem_lt b a) (not (a == b))

let[@axiom] elem2 ((a [@forall]) : Elem.t) = not (elem_lt a a)

let[@axiom] elem3 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies (elem_lt a b) (not (elem_lt b a))

let[@axiom] elem4 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t)
    ((c [@forall]) : Elem.t) =
  implies (elem_lt a b && elem_lt b c) (elem_lt a c)
