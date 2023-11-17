let[@axiom] bytes2 ((content [@forall]) : Bytes.t) =
  not (is_dir content && is_del content)

let[@axiom] path1 ((path [@forall]) : Path.t) = not (path == parent path)

let[@axiom] elem1 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies (elem_lt a b || elem_lt b a) (not (a == b))

let[@axiom] elem2 ((a [@forall]) : Elem.t) = not (elem_lt a a)

let[@axiom] elem3 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies (elem_lt a b) (not (elem_lt b a))

let[@axiom] elem4 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t)
    ((c [@forall]) : Elem.t) =
  implies (elem_lt a b && elem_lt b c) (elem_lt a c)
