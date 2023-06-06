From stdpp Require Import mapset.
From CT Require Import Tactics.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

(** The trace are always locally closed *)
Inductive trace : Type :=
| ϵ
| trretv (v: value)
| trseq (op: effop) (argv: constant) (retv: constant) (tr: trace).

Coercion trretv : value >-> trace.

Notation " 'tr{' op ',' v1 ',' v2 '}' " := (trseq op v1 v2 ϵ)
                                        (at level 20, format "tr{ op , v1 , v2 }",
                                          op constr, v1 constr, v2 constr, right associativity).

Notation " 'tr{' op ',' v1 ',' v2 '}::' α " := (trseq op v1 v2 α)
                                        (at level 20, format "tr{ op , v1 , v2 }:: α",
                                          op constr, v1 constr, v2 constr, right associativity).

Fixpoint trace_app (tr1 tr2: trace): trace :=
  match tr1 with
  | ϵ => tr2
  | trretv _ => tr2
  | tr{ op, v1, v2 }:: α => tr{ op , v1, v2 }:: (trace_app α tr2)
  end.

Notation " a '+;+' b" := (trace_app a b) (at level 20, a constr, b constr, right associativity).

Inductive with_retv: trace -> Prop :=
| with_retv_retv: forall v, with_retv (trretv v)
| with_retv_seq: forall op v1 v2 e, with_retv e -> with_retv (tr{ op,  v1, v2 }:: e).

Theorem tr_app_ϵ_end : forall tr, tr = tr +;+ ϵ.
Admitted.

Theorem tr_app_ϵ_start : forall tr, tr = ϵ +;+ tr.
Proof. auto. Qed.

Theorem tr_app_ass : forall l m n, (l +;+ m) +;+ n = l +;+ m +;+ n.
Admitted.

Theorem tr_ass_app : forall l m n, l +;+ m +;+ n = (l +;+ m) +;+ n.
Proof.
    auto using tr_app_ass.
Qed.

Theorem tr_app_comm_cons : forall x y op v1 v2, tr{ op, v1 , v2 }:: (x +;+ y) = (tr{ op, v1, v2 }:: x) +;+ y.
Proof.
  auto.
Qed.

Theorem tr_app_cons_not_ϵ : forall x y op v1 v2, ϵ <> x +;+ tr{op, v1, v2}:: y.
Admitted.

Theorem tr_app_eq_ϵ : forall l l', l +;+ l' = ϵ -> l = ϵ  /\ l' = ϵ .
Admitted.

Theorem app_eq_unit :
    forall x y op v1 v2,
      x +;+ y = tr{op, v1, v2} -> x = ϵ /\ y = tr{ op, v1, v2} \/ x = tr{ op, v1, v2} /\ y = ϵ.
Admitted.

Lemma app_inj_tail :
    forall (x y:trace) op_a op_b (a1 a2 b1 b2: constant),
      x +;+ tr{op_a, a1, a2} = y +;+ tr{op_b, b1, b2} -> x = y /\ a1 = b1 /\ a2 = b2.
Admitted.

Definition tr_reduction: trace -> effop -> constant -> constant -> Prop.
Admitted.

Notation " 'app{' op ',' c1 '}⇓{' α '}' c" := (tr_reduction α op c1 c)
                                          (at level 30, format "app{ op , c1 }⇓{ α } c", c1 constr, α constr).


