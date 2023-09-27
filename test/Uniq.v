From stdpp Require Import stringmap mapset natmap.
From stdpp Require Export prelude fin_maps fin_map_dom.
From Hammer Require Export Tactics.

Inductive event : Type :=
| Push (n: nat)
| Pop (n: nat)
| Other.

Global Hint Constructors event : core.

Inductive sevent : Type :=
| PushS (ϕ: nat -> Prop)
| PopS (ϕ: nat -> Prop)
| OtherS.

Global Hint Constructors sevent : core.

Inductive srtl : Type :=
| Sev (sev: sevent)
| ϵ
| AnyA
| NegA (P: srtl)
| AndA (P1: srtl) (P2: srtl)
| OrA (P1: srtl) (P2: srtl)
| SeqA (P1: srtl) (P2: srtl)
| StarA (P: srtl)
| CtxA (sev: sevent) (P: srtl).

Global Hint Constructors srtl : core.

Notation "a '+A+' b " := (SeqA a b) (at level 20, format "a +A+ b", a constr, b constr).
Notation "∙" := AnyA (at level 20, format "∙").
Notation "∙*" := (StarA AnyA) (at level 20, format "∙*").
Notation "'\\{' sev '}' P " := (CtxA sev P) (at level 20, format "\\{ sev } P", sev constr, P constr).

Fixpoint sevR (sev: sevent) (ev: event) : Prop :=
  match sev with
  | PushS ϕ =>
      match ev with
      | Push n => ϕ n
      | _ => False
      end
  | PopS ϕ =>
      match ev with
      | Pop n => ϕ n
      | _ => False
      end
  | OtherS => ev = Other
  end.

Inductive repeat_tr: (list event -> Prop) -> list event -> Prop :=
| repeat_tr0: forall p, repeat_tr p []
| repeat_tr1: forall (p: list event -> Prop) α β, p α -> repeat_tr p β -> repeat_tr p (α ++ β).

Global Hint Constructors repeat_tr: core.

Fixpoint srtlR (E: event -> Prop) (P: srtl) (tr: list event) : Prop :=
  match P with
  | Sev sev => exists ev, tr = [ev] /\ sevR sev ev
  | ϵ => tr = []
  | AnyA => exists ev, tr = [ev] /\ E ev
  | NegA P => repeat_tr (fun tr => exists ev, tr = [ev] /\ E ev) tr /\ ~ srtlR E P tr
  | AndA P1 P2 => srtlR E P1 tr /\ srtlR E P2 tr
  | OrA P1 P2 => srtlR E P1 tr \/ srtlR E P2 tr
  | SeqA P1 P2 => exists tr1 tr2, tr = tr1 ++ tr2 /\ srtlR E P1 tr1 /\ srtlR E P2 tr2
  | StarA P => repeat_tr (srtlR E P) tr
  | CtxA sev P => srtlR (fun ev => E ev /\ ~ sevR sev ev) P tr
  end.

Inductive trace_as_set: natset -> list event -> natset -> Prop :=
| trace_as_set0: forall s, trace_as_set s [] s
| trace_as_set1: forall s s' n tr,
    n ∉ s ->
    trace_as_set ({[n]} ∪ s) tr s' ->
    trace_as_set s ((Push n) :: tr) s'
| trace_as_set2: forall s s' n tr,
    n ∉ s ->
    trace_as_set (s ∖ {[n]}) tr s' ->
    trace_as_set s ((Pop n) :: tr) s'
| trace_as_set3:
  forall s s' tr, trace_as_set s tr s' -> trace_as_set s (Other :: tr) s'.

Notation "s '⥬{' tr '}' s' " := (trace_as_set s tr s')
                                   (at level 20, format "s ⥬{ tr } s'", s constr, tr constr, s' constr).

Global Hint Constructors trace_as_set: core.

Definition spec (x: nat) :=
  ∙* +A+ (Sev (PushS (fun n => n = x))) +A+ (\\{ PopS (fun n => n = x) } ∙*) +A+ (Sev (PushS (fun n => n = x))) +A+ ∙*.

Definition uniq_trace_sfa (tr: list event) := forall x, srtlR (fun _ => True) (NegA (spec x)) tr.

Definition uniq_trace_coq (tr: list event) := forall n,
    ~ (exists tr1 tr2 tr3, tr = tr1 ++ [Push n] ++ tr2 ++ [Push n] ++ tr3 /\ ~ In (Pop n) tr2).

Lemma uniq_trace_sfa_sound: forall tr, uniq_trace_coq tr ->
    forall tr1 tr2 s0 s1, tr = tr1 ++ tr2 ->
                 s0 ⥬{ tr1 } s1 -> (exists s2, s1 ⥬{ tr2 } s2).
Proof.
  intros tr. induction tr; intros Hspec tr1 tr2 s0 s1 Heq Htr1; subst.
  - admit.
  -  assert (uniq_trace_coq tr) as Hi. admit.
    specialize (IHtr Hi). clear Hi.
    destruct tr1. simpl in Heq. subst.
    + inversion Htr1; subst; clear Htr1.
      destruct a; eauto.
      * specialize (IHtr tr [] {[n]}  ({[n]} ∪ s1)).

    { apply IHtr with (tr1 := []) (s0 := s0); auto. }
    rewrite <- app_comm_cons in Heq. inversion Heq; subst; clear Heq.
   
    destruct e; inversion Htr1; subst; clear Htr1; eauto.

      specialize (IHtr tr1 tr2 ({[n]} ∪ s0) s1).
      destruct IHtr; eauto.
    + inversion Htr1; subst; clear Htr1.
      specialize (IHtr tr1 tr2 (s0 ∖ {[n]}) s1).
      destruct IHtr; eauto.
    + inversion Htr1; subst; clear Htr1; eauto.
      specialize (IHtr tr1 tr2 s0 s1). eauto.

      apply IHtr in H4.
  induction tr; intros s Hs Hspec; subst; eauto. destruct a.
  - inversion Hspec; subst; auto.

  - exists s; auto.
    apply IHtr with (l := (n :: l)); eauto. admit.
  - 

  induction Hst; auto.
  - apply IHHst.
  Hl s' Hst.
