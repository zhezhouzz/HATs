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

(* Definition trace : Type := list evop * option value. *)
Definition trace : Type := list evop.

(* Definition ϵ : trace := ([], None). *)

(* Definition trace_app (tr1 tr2: trace): trace := *)
(*   (tr1.1 ++ tr2.1, tr2.2). *)

(* Notation " a '+;+' b" := (trace_app a b) (at level 20, a constr, b constr, right associativity). *)

(* Theorem tr_app_ϵ_end : forall tr, tr = tr +;+ ϵ. *)
(* Admitted. *)

(* Theorem tr_app_ϵ_start : forall tr, tr = ϵ +;+ tr. *)
(* Proof. intros. simpl. destruct tr. auto. Qed. *)

(* Theorem tr_app_ass : forall l m n, (l +;+ m) +;+ n = l +;+ m +;+ n. *)
(* Admitted. *)

(* Theorem tr_ass_app : forall l m n, l +;+ m +;+ n = (l +;+ m) +;+ n. *)
(* Proof. *)
(*     auto using tr_app_ass. *)
(* Qed. *)

(* Theorem tr_app_comm_cons : forall x y op v1 v2, tr{ op, v1 , v2 }:: (x +;+ y) = (tr{ op, v1, v2 }:: x) +;+ y. *)
(* Proof. *)
(*   auto. *)
(* Qed. *)

(* Theorem tr_app_cons_not_ϵ : forall x y op v1 v2, ϵ <> x +;+ tr{op, v1, v2}:: y. *)
(* Admitted. *)

(* Theorem tr_app_eq_ϵ : forall l l', l +;+ l' = ϵ -> l = ϵ  /\ l' = ϵ . *)
(* Admitted. *)

(* Theorem app_eq_unit : *)
(*     forall x y op v1 v2, *)
(*       x +;+ y = tr{op, v1, v2} -> x = ϵ /\ y = tr{ op, v1, v2} \/ x = tr{ op, v1, v2} /\ y = ϵ. *)
(* Admitted. *)

(* Lemma app_inj_tail : *)
(*     forall (x y:trace) op_a op_b (a1 a2 b1 b2: constant), *)
(*       x +;+ tr{op_a, a1, a2} = y +;+ tr{op_b, b1, b2} -> x = y /\ a1 = b1 /\ a2 = b2. *)
(* Admitted. *)

Definition tr_reduction: list evop -> effop -> constant -> constant -> Prop.
Admitted.

Notation "α '⊧{' op '~' c1 '}⇓{' c '}' " := (tr_reduction α op c1 c)
                                              (at level 30, format "α ⊧{ op ~ c1 }⇓{ c }", c1 constr, α constr).
