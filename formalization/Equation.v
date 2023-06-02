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
| trevent (op: effop) (v: value)
| trseq (op: effop) (v: value) (tr: trace).

Coercion trretv : value >-> trace.

Notation " op ':{' v  '}' " := (trevent op v) (at level 20, op constr, v constr, right associativity).

Notation " op ':{' v  '};' e" := (trseq op v e) (at level 20, op constr, v constr, e constr, right associativity).

Fixpoint trace_app (tr1 tr2: trace): trace :=
  match tr1 with
  | ϵ => tr2
  | trretv _ => tr2
  | trevent op v => op :{ v }; tr2
  | (trseq op v tr1) => op :{ v }; (trace_app tr1 tr2)
  end.

Notation " a '+;+' b" := (trace_app a b) (at level 20, a constr, b constr, right associativity).

Inductive with_retv: trace -> Prop :=
| with_retv_retv: forall v, with_retv (trretv v)
| with_retv_seq: forall op v e, with_retv e -> with_retv (op :{ v }; e).

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

Theorem tr_app_comm_cons : forall x y op v, op :{ v }; (x +;+ y) = (op :{ v }; x) +;+ y.
Proof.
  auto.
Qed.

Theorem tr_app_cons_not_ϵ : forall x y op v, ϵ <> x +;+ op :{v}; y.
Admitted.

Theorem tr_app_eq_ϵ : forall l l', l +;+ l' = ϵ -> l = ϵ  /\ l' = ϵ .
Admitted.

Theorem app_eq_unit :
    forall x y op a,
      x +;+ y = op :{a}; ϵ -> x = ϵ /\ y = op :{a}; ϵ \/ x = op :{a}; ϵ /\ y = ϵ.
Admitted.

Lemma app_inj_tail :
    forall (x y:trace) op_a op_b (a b: value), x +;+ op_a :{a}; ϵ = y +;+ op_b :{b}; ϵ -> x = y /\ a = b.
Admitted.

Definition tr_reduction: trace -> trace -> Prop.
Admitted.

Notation " a '⇓' b" := (tr_reduction a b) (at level 30, a constr, b constr).
