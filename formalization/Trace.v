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

Inductive read_reduction : trace -> constant -> Prop :=
| ReadRead: forall (α: trace) (n: nat) (b: bool), read_reduction (α ++ [ev{ op_read ~ n := b }]) n
| WriteRead: forall (α: trace) (n: nat) (b: bool), read_reduction (α ++ [ev{ op_write ~ b := n }]) n
| ElseRead: forall (α: trace) op c c' (n: nat),
    ~ (op = op_read) -> ~ (op = op_write) ->
    read_reduction α n -> read_reduction (α ++ [ev{ op ~ c := c' }]) n.

Inductive tr_reduction : trace -> effop -> constant -> constant -> Prop :=
| TrPlus1: forall (α: trace) (n: nat), tr_reduction α op_plus_one n (S n)
| TrMinus1: forall (α: trace) (n: nat), tr_reduction α op_minus_one (S n) n
| TrEq0_0: forall (α: trace), tr_reduction α op_eq_zero 0 true
| TrEq0_S: forall (α: trace) (n: nat), tr_reduction α op_eq_zero (S n) false
| TrNatGen: forall (α: trace) (n: nat) (n': nat), tr_reduction α op_rannat n n'
| TrBoolGen: forall (α: trace) (n: nat) (b: bool), tr_reduction α op_ranbool n b
| TrWrite: forall (α: trace) (n: nat) (b: bool), tr_reduction α op_write n b
| TrRead: forall (α: trace) (n: nat) (b: bool), read_reduction α n -> tr_reduction α op_read n b.

Notation "α '⊧{' op '~' c1 '}⇓{' c '}' " := (tr_reduction α op c1 c)
                                              (at level 30, format "α ⊧{ op ~ c1 }⇓{ c }", c1 constr, α constr).
