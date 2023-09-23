type tree = E | T of tree * elem * tree

let pre_order = function
  | T (E, x, E) -> x
  | T (left, x, right) -> x :: (post_order left @ post_order right)

let rec insert x = function
  | E -> T (E, x, E)
  | T (a, y, b) as s ->
      if Element.lt x y then T (insert x a, y, b)
      else if Element.lt y x then T (a, y, insert x b)
      else s

let rec bst_gen (l : int list) : int tree =
  match l with [] -> E | h :: t -> insert h (bst_gen l)

bst_gen: l:{v:int list|top} -> []

(* x:{v:int|top} -> tr:{v:int tree| bst v} ->
   [v: int tree | if mem tr x then v = tr else exists l1 l2. preorder l1 ++ l2 tr /\ preorder (l1 ++ x ++ l2) v /\ bst v] *)

(* x:{v:int|top}, y:{v:int| x < v}, a:{v:int tree| bst v /\ forall u, mem v u => u < y}, b:{v:int tree| bst v /\ forall u, mem v u => u > y} *)
(* tmp: [v: int tree | exists l1 l2. preorder l1 ++ l2 a /\ preorder (l1 ++ x ++ l2) v /\ bst v] *)
(* [v: int tree | exists l1 l2. preorder l1 ++ l2 a /\ preorder (y :: l1 ++ x ++ l2 ++ lb) v /\ bst v /\ preorder bl b] *)
(* [v: int tree | exists l1 l2. preorder l1 ++ l2 b /\ preorder (y :: la ++ l1 ++ x ++ l2) v /\ bst v /\ preorder al a] *)
