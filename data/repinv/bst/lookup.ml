type effect =
  | Put of (int -> int -> int -> unit)
  | Get of (int -> int -> int)
  | FreshKey of (int -> int)

type bst = int
type node = int

let ltab = 0 (* (node -> node) left child table *)
let rtab = 1 (* (node -> node) right child table *)
let root_tab = 2 (* (bst -> node) recode the root of bst *)
let vtab = 3 (* (node -> 'a) recode the value in the node *)
let void = -1 (* negative node means unintialized *)
let is_void_node (n : node) = n < 0

let rec lookup (bst : bst) (x : int) : bool =
  let (root : node) = get root_tab bst in
  if root < 0 then false
  else
    let (v : int) = get vtab root in
    let (b0 : bool) = v == x in
    let (lnode : node) = get ltab root in
    let () = put root_tab bst lnode in
    let (b1 : bool) = lookup x in
    let () = put root_tab bst rnode in
    let (b2 : bool) = lookup x in
    let () = put root_tab bst root in
    b0 || b1 || b2

let rec insert (bst : bst) (x : int) : bool =
  let (root : node) = get root_tab bst in
  if root < 0 then (
    let (root' : int) = freshKey vtab in
    put vtab root' x;
    put root_tab bst root')
  else
    let (v : int) = get vtab root in
    if x == v then ()
    else if x < v then (
      put root_tab bst (get ltab root);
      insert bst x;
      put root_tab bst root)
    else (
      put root_tab bst (get rtab root);
      insert bst x;
      put root_tab bst root)

(* min_val return -1 over empty tree *)
let rec min_val (bst : bst) : int =
  let (root : node) = get root_tab bst in
  if root < 0 then -1
  else
    let (lnode : node) = get ltab root in
    if lnode < 0 then root
    else
      let () = put root_tab bst lnode in
      let min = min_val bst in
      let () = put root_tab bst root in
      min

let rec delete (bst : bst) (x : int) : bool =
  let (root : node) = get root_tab bst in
  if root < 0 then ()
  else if root == x then (
    let (lnode : node) = get ltab root in
    let (rnode : node) = get rtab root in
    if lnode < 0 then
      if rnode < 0 then put root_tab bst void else put root_tab bst rnode
    else if rnode < 0 then put root_tab bst lnode
    else
      let min = min_val () in
      put ltab min lnode;
      put root_tab bst rnode;
      put rtab node void;
      delete bst min;
      put rtab min (get root_tab bst);
      put root_tab bst min)
  else if x < root then (
    put root_tab bst (get ltab root);
    put rtab node void;
    delete bst x;
    put ltab root (get root_tab bst);
    put root_tab bst root)
  else (
    put root_tab bst (get rtab root);
    delete bst x;
    put rtab root (get root_tab bst);
    put root_tab bst root)

let rec copy (dest : bst) (origin : bst) : unit =
  let () = put root_tab dest void in
  let (root : node) = get root_tab origin in
  if root < 0 then ()
  else
    let (v : int) = get vtab root in
    let (root' : int) = freshKey vtab in
    let (lnode' : int) = freshKey vtab in
    let (rnode' : int) = freshKey vtab in
    put root_tab dest lnode';
    copy dest (get ltab root);
    put root_tab dest rnode';
    copy dest (get rtab root);
    put vtab root' v;
    put ltab root' lnode';
    put rtab root' rnode';
    put dest root'

let rec union (bst1 : bst) (bst2 : bst) : unit =
  let (root : node) = get root_tab bst1 in
  if root < 0 then copy bst1 bst2
  else
    let (v : int) = get vtab root in
    let (lnode : node) = get ltab root in
    let (rnode : node) = get rtab root in
    put ltab root void;
    put rtab root void;
    put root_tab bst1 lnode;
    union bst1 bst2;
    put root_tab bst2 rnode;
    union bst1 bst2;
    insert bst1 v

let rec inter (bst1 : int) (bst2 : int) : unit =
  let (root : node) = get root_tab bst1 in
  if root < 0 then put root_tab bst1 void
  else
    let (lnode : node) = get ltab root in
    let (rnode : node) = get rtab root in
    put ltab root void;
    put rtab root void;
    put root_tab bst1 lnode;
    inter bst1 bst2;
    put root_tab bst1 rnode;
    inter bst1 bst2;
    put root_tab bst1 lnode;
    put root_tab bst2 rnode;
    union bst1 bst2;
    if lookup bst2 root then insert bst1 root else ()
