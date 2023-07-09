From stdpp Require Import mapset.
From CT Require Import Tactics.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import Lists.List.

Inductive evop : Type :=
| evop_ (op: effop) (argv: constant) (retv: constant).

Notation " 'ev{' op '~' v1 ':=' v2 '}' " := (evop_ op v1 v2)
                                        (at level 20, format "ev{ op ~ v1 := v2 }",
                                          op constr, v1 constr, v2 constr, right associativity).

Definition trace : Type := list evop.

Parameter tr_reduction: list evop -> effop -> constant -> constant -> Prop.

Notation "α '⊧{' op '~' c1 '}⇓{' c '}' " := (tr_reduction α op c1 c)
                                              (at level 30, format "α ⊧{ op ~ c1 }⇓{ c }", c1 constr, α constr).
