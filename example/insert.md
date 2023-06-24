Dear John,

If I understand correctly, you plan to built a binary search tree generator as the following:

```
let rec bst_gen (l: int list) : int tree =
  match l with
  | [] -> Leaf
  | h :: t -> insert t (bst_gen t)

l:{v:int list| \top} -> [v:int tree | mem l = mem v /\ bst v]

x:{\top} -> t:{v:int tree | bst v} -> [v:int tree | mem t \cup x = mem v /\ bst v]

|- bst_gen (list_gen ()) : [v:int tree | bst v ]
```

[1;2;3]

1
2
3

 2
1 3
and we want to know if it is coverage complete, which means the term `bst_gen (list_gen ())` has the top coverage type if `list_gen ()` has 
I believe this question is depends on how you impelement the `insert` function -- if it is a stardard deterministic insert function, this generator has no chance to be complete, and will have a type error in our coverage type system. I believe the specification of 
