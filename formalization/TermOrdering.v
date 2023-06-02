From stdpp Require Import mapset.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import OperationalSemanticsProp.
Import BasicTyping.
Import ListCtx.
Import SyntaxSugar.

(** * We define a patial order over the well-typed terms which is derived from the values they can reduced to. It works similar with the "instantiation" in the proof of the normalization of STLC: https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html#instantiation However, our language has randomness, thus a term can reduce to multiple vaules, thus we build a patial order relation. *)

Definition env := listctx value.
Fixpoint tm_msubst (ss:env) (t:tm) : tm :=
  match ss with
  | nil => t
  | ((x,s)::ss') => tm_msubst ss' ({x := s}t t)
  end.

Fixpoint value_msubst (ss:env) (t:value) : value :=
  match ss with
  | nil => t
  | ((x,s)::ss') => value_msubst ss' ({x := s}v t)
  end.

Inductive instantiation : (listctx ty) -> env -> Prop :=
| instantiation_nil: instantiation [] []
| instantiation_cons: forall x T (v: value) c e,
    [] ⊢t v ⋮v T ->
    x ∉ ctxdom c ->
    instantiation c e ->
    instantiation ((x, T) :: c) ((x, v) :: e).

Global Hint Constructors instantiation: core.

Lemma instantiation_regular_ok: forall Γt Γv, instantiation Γt Γv -> ctxdom Γt = ctxdom Γv /\ ok Γt /\ ok Γv.
Proof.
  intros. induction H; repeat destruct_hyp_conj; repeat split; intros; auto;
    try  listctx_set_solver;
  try (simpl; rewrite H2; auto; try listctx_set_solver).
  - rewrite ok_pre_destruct; split; auto. rewrite <- H2; auto.
Qed.

Lemma instantiation_regular_lc: forall Γt Γv, instantiation Γt Γv -> (forall x v, ctxfind Γv x = Some v -> lc v).
Proof.
  intros. assert (ok Γv). apply instantiation_regular_ok in H. repeat destruct_hyp_conj; auto.
  induction H; simpl; auto.
  - simpl in H0. listctx_set_solver.
  - simpl in H0. repeat var_dec_solver; basic_typing_solver.
Qed.

Lemma instantiation_regular_closed: forall Γt Γv, instantiation Γt Γv -> (forall x v, ctxfind Γv x = Some v -> closed_value v).
Proof.
  intros. assert (ok Γv). apply instantiation_regular_ok in H. repeat destruct_hyp_conj; auto.
  induction H; auto.
  - listctx_set_solver.
  - simpl in H0. repeat var_dec_solver;
    basic_typing_solver3.
Qed.

Lemma instantiation_regular: forall Γt Γv, instantiation Γt Γv ->
                                      (forall x v, ctxfind Γv x = Some v -> lc v) /\
                                        (forall x v, ctxfind Γv x = Some v -> closed_value v) /\
                                        ctxdom Γt = ctxdom Γv /\ ok Γt /\ ok Γv.
Proof.
  intros. split.
  eapply instantiation_regular_lc; eauto.
  split.
  eapply instantiation_regular_closed; eauto.
  apply instantiation_regular_ok; auto.
Qed.


Lemma tm_msubst_closed: ∀ e, closed_tm e -> (forall ss, tm_msubst ss e = e).
Proof.
  unfold closed_tm.
  intros.
  induction ss; simpl; auto.
  destruct a. rewrite subst_fresh_tm; auto. fast_set_solver!!.
Qed.

Lemma value_msubst_closed: ∀ e, closed_value e -> (forall ss, value_msubst ss e = e).
Proof.
  unfold closed_value.
  intros.
  induction ss; simpl; auto.
  destruct a. rewrite subst_fresh_value; auto. fast_set_solver!!.
Qed.

Lemma instantiation_R : ∀ c e,
    instantiation c e →
    ∀ x t T,
      ctxfind c x = Some T →
      ctxfind e x = Some t → [] ⊢t t ⋮t T.
Proof.
  intros c e V. induction V; simpl ; intros.
  - inversion H.
  - repeat var_dec_solver.
    eapply IHV; eauto.
Qed.

Lemma instantiation_R_exists : ∀ c e,
    instantiation c e →
    ∀ x T,
      ctxfind c x = Some T →
      (exists t, ctxfind e x = Some t /\ [] ⊢t t ⋮t T /\ closed_value t).
Proof.
  intros c e V. induction V; simpl ; intros.
  - inversion H.
  - repeat var_dec_solver. exists v. split; auto. split; auto; basic_typing_solver3.
Qed.

Lemma msubst_var: ∀ ss (x: atom) (v: value), closed_value v -> ctxfind ss x = Some v -> value_msubst ss x = v.
Proof.
  induction ss; simpl; intros.
  - inversion H0.
  - destruct a. repeat var_dec_solver. rewrite value_msubst_closed; auto.
Qed.

Lemma msubst_var_none: ∀ ss (x: atom), ctxfind ss x = None -> value_msubst ss x = x.
Proof.
  induction ss; simpl; intros; auto.
  - destruct a. repeat var_dec_solver.
Qed.

Lemma msubst_vlam: ∀ ss Tx e, value_msubst ss (vlam Tx e) = vlam Tx (tm_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_open_tm: ∀ Γv e k (x: atom),
  ok Γv ->
  (forall x v, ctxfind Γv x = Some v -> closed_value v /\ lc v) ->
  x ∉ ctxdom Γv ->
  {k ~t> x} (tm_msubst Γv e) = tm_msubst Γv ({k ~t> x} e).
Proof.
  induction Γv; simpl; intros; auto.
  - auto_destruct_pair.
    assert (closed_value v /\ lc v). eapply (H0 a v); eauto. repeat var_dec_solver.
    rewrite subst_open_var_tm.
    rewrite IHΓv; auto. listctx_set_solver.
    intros. specialize (H0 x0 v0). repeat var_dec_solver. apply ctxfind_some_implies_in_dom in H3. rewrite ok_pre_destruct in H. destruct H. fast_set_solver. fast_set_solver. fast_set_solver. destruct H2; auto.
Qed.

Lemma msubst_open_value: ∀ Γv e k (x: atom),
  ok Γv ->
  (forall x v, ctxfind Γv x = Some v -> closed_value v /\ lc v) ->
  x ∉ ctxdom Γv ->
  {k ~v> x} (value_msubst Γv e) = value_msubst Γv ({k ~v> x} e).
Proof.
  induction Γv; simpl; intros; auto.
  - auto_destruct_pair.
    assert (closed_value v /\ lc v). eapply (H0 a v); eauto. repeat var_dec_solver.
    rewrite subst_open_var_value.
    rewrite IHΓv; auto. listctx_set_solver.
    intros. specialize (H0 x0 v0). repeat var_dec_solver. apply ctxfind_some_implies_in_dom in H3. rewrite ok_pre_destruct in H. destruct H. fast_set_solver. fast_set_solver. fast_set_solver. destruct H2; auto.
Qed.

Ltac instantiation_regular_solver :=
  match goal with
  | [H: instantiation ?a ?b |- _ ∉ _ ] =>
      apply instantiation_regular in H; repeat destruct_hyp_conj; auto; listctx_set_simpl; set_solver
  | [H: instantiation ?a ?b |- ok _ ] =>
      apply instantiation_regular_ok in H; repeat destruct_hyp_conj; auto; listctx_set_solver
  | [H: instantiation ?a ?b |- forall x v, ctxfind ?b x = Some v -> _ ] =>
      apply instantiation_regular in H; repeat destruct_hyp_conj; eauto; listctx_set_solver
  end.

Lemma msubst_vfix: ∀ ss Tx (e: value), value_msubst ss (vfix Tx e) = vfix Tx (value_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_value: ∀ ss (v: value), tm_msubst ss v = tvalue (value_msubst ss v).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tlete: ∀ ss e1 e2, tm_msubst ss (tlete e1 e2) = tlete (tm_msubst ss e1) (tm_msubst ss e2).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tletbiop: ∀ ss op v1 v2 e,
    tm_msubst ss (tletbiop op v1 v2 e) = tletbiop op (value_msubst ss v1) (value_msubst ss v2) (tm_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tletapp: ∀ ss v1 v2 e,
    tm_msubst ss (tletapp v1 v2 e) = tletapp (value_msubst ss v1) (value_msubst ss v2) (tm_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tmatchb: ∀ ss v e1 e2,
    tm_msubst ss (tmatchb v e1 e2) = tmatchb (value_msubst ss v) (tm_msubst ss e1) (tm_msubst ss e2).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_vbvar: ∀ ss k, value_msubst ss (vbvar k) = (vbvar k).
Proof.
  induction ss; simpl; intros; mydestr; auto.
Qed.

Lemma msubst_terr: ∀ ss, tm_msubst ss terr = terr.
Proof.
  induction ss; simpl; intros; auto.
  - destruct a. auto.
Qed.

Ltac msubst_simpl :=
  repeat match goal with
    | [H: context [value_msubst ?env (vbvar ?k)] |- _ ] =>
        setoid_rewrite (msubst_vbvar env k) in H
    | [ |- context [value_msubst ?env (vbvar ?k)] ] =>
        setoid_rewrite (msubst_vbvar env k)
    | [H: context [value_msubst ?env (vlam ?Tx ?e)] |- _ ] =>
        setoid_rewrite (msubst_vlam env Tx) in H
    | [ |- context [value_msubst ?env (vlam ?Tx ?e)] ] =>
        setoid_rewrite (msubst_vlam env Tx)
    | [H: context [value_msubst ?env (vfix ?Tx ?e)] |- _ ] =>
        setoid_rewrite (msubst_vfix env Tx) in H
    | [ |- context [value_msubst ?env (vfix ?Tx ?e)] ] =>
        setoid_rewrite (msubst_vfix env Tx)
    | [H: context [tm_msubst ?env (tvalue ?v)] |- _ ] =>
        setoid_rewrite (msubst_value env v) in H
    | [ |- context [tm_msubst ?env (tvalue ?v)] ] =>
        setoid_rewrite (msubst_value env v)
    | [H: context [tm_msubst ?env (tlete ?e1 ?e2)] |- _ ] =>
        setoid_rewrite (msubst_tlete env e1 e2) in H
    | [ |- context [tm_msubst ?env (tlete ?e1 ?e2)] ] =>
        setoid_rewrite (msubst_tlete env e1 e2)
    | [H: context [tm_msubst ?env (tletbiop ?op ?v1 ?v2 ?e)] |- _ ] =>
        setoid_rewrite (msubst_tletbiop env op v1 v2 e) in H
    | [ |- context [tm_msubst ?env (tletbiop ?op ?v1 ?v2 ?e)] ] =>
        setoid_rewrite (msubst_tletbiop env op v1 v2 e)
    | [H: context [tm_msubst ?env (tletapp ?v1 ?v2 ?e)] |- _ ] =>
        setoid_rewrite (msubst_tletapp env v1 v2 e) in H
    | [ |- context [tm_msubst ?env (tletapp ?v1 ?v2 ?e)] ] =>
        setoid_rewrite (msubst_tletapp env v1 v2 e)
    | [H: context [tm_msubst ?env (tmatchb ?v ?e1 ?e2)] |- _ ] =>
        setoid_rewrite (msubst_tmatchb env v e1 e2) in H
    | [ |- context [tm_msubst ?env (tmatchb ?v ?e1 ?e2)] ] =>
        setoid_rewrite (msubst_tmatchb env v e1 e2)
    | [H: context [tm_msubst ?env terr] |- _ ] => rewrite (msubst_terr env) in H
    | [ |- context [tm_msubst ?env terr] ] => rewrite (msubst_terr env)
    end.

Lemma closed_has_type_under_any_ctx_value: forall Γ (v: value) T, Γ ⊢t v ⋮v T -> closed_value v -> (forall Γ', ok Γ' -> Γ' ⊢t v ⋮v T).
Proof.
  intros. apply closed_has_type_under_empty_value in H; auto. basic_typing_solver2.
Qed.

Lemma closed_has_type_under_any_ctx_tm: forall Γ (v: tm) T, Γ ⊢t v ⋮t T -> closed_tm v -> (forall Γ', ok Γ' -> Γ' ⊢t v ⋮t T).
Proof.
  intros. apply closed_has_type_under_empty_tm in H; auto. basic_typing_solver2.
Qed.

Ltac msubst_preserves_typing_tac :=
  match goal with
  | [a: atom |- _ ] => repeat specialize_with a
  end;
  repeat match goal with
    | [|- _ ⊢t ((tm_msubst _ _) ^t^ _) ⋮t _ ] =>
        rewrite msubst_open_tm; try instantiation_regular_solver; try fast_set_solver
    | [|- _ ⊢t ((value_msubst _ _) ^v^ _) ⋮v _ ] =>
        rewrite msubst_open_value; try instantiation_regular_solver; try fast_set_solver
    | [H: context [_ ⊢t (tm_msubst _ _) ⋮t ?T] |- _ ⊢t _ ⋮t ?T] =>
        eapply H; eauto; try (rewrite app_assoc; auto)
    end.

Ltac msubst_preserves_typing_tac2 :=
  (repeat match goal with
     | [|- closed_value _] => unfold closed_value; intros; listctx_set_solver
     | [ |- _ ⊢t mk_app _ _ ⋮t ?T ] => eapply mk_app_typable; eauto
     | [ |- _ ⊢t (value_msubst _ _) ⋮v ?T ] => rewrite value_msubst_closed
     | [ |- _ ⊢t (tvalue (value_msubst _ _)) ⋮t ?T ] => rewrite value_msubst_closed
     end; basic_typing_solver2).

Lemma msubst_preserves_typing_tm_aux: ∀ Γ e T,
    Γ ⊢t e ⋮t T -> (forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (tm_msubst Γv e) ⋮t T).
Proof.
  apply (tm_has_type_mutual_rec
           (fun Γ v T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (value_msubst Γv v) ⋮v T)
           (fun Γ e T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (tm_msubst Γv e) ⋮t T)
        ); simpl; intros; subst; listctx_set_simpl; repeat destruct_hyp_conj; msubst_simpl; eauto;
  try (msubst_preserves_typing_tac2; constructor; listctx_set_solver);
  try (auto_exists_L; simpl; intros; msubst_preserves_typing_tac).
  - assert (forall x v, ctxfind Γv x = Some v -> closed_value v). eapply instantiation_regular_closed; eauto.
    rewrite ctxfind_app in e; auto. destruct e.
    + eapply instantiation_R_exists in H0; eauto. destruct H0 as (v & Hv1 & Hv2 & Hv3).
      erewrite msubst_var; eauto. basic_typing_solver2.
    + rewrite msubst_var_none; basic_typing_solver2.
      apply instantiation_regular_ok in H0. mydestr. rewrite <- H0.
      apply ctxfind_app_exclude in o. my_set_solver.
  - (* auto_exists_L; simpl; intros. repeat specialize_with f. *)
    msubst_preserves_typing_tac.
    specialize (H Γt (Γt' ++ [(f, TBase Tx)]) Γv).
    rewrite msubst_vlam in H.
    rewrite msubst_open_tm; try instantiation_regular_solver. apply H; auto.
    rewrite app_assoc; auto.
Qed.

Lemma msubst_preserves_typing_tm: ∀ Γ Γv e T,
    Γ ⊢t e ⋮t T -> instantiation Γ Γv -> [] ⊢t (tm_msubst Γv e) ⋮t T.
Proof.
  intros. eapply msubst_preserves_typing_tm_aux; eauto. listctx_set_simpl.
Qed.

Lemma msubst_preserves_typing_value_aux: ∀ Γ (e: value) T,
    Γ ⊢t e ⋮v T -> (forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (value_msubst Γv e) ⋮v T).
Proof.
  apply (value_has_type_mutual_rec
           (fun Γ v T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (value_msubst Γv v) ⋮v T)
           (fun Γ e T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (tm_msubst Γv e) ⋮t T)
        ); simpl; intros; subst; listctx_set_simpl; repeat destruct_hyp_conj; msubst_simpl; eauto;
  try (msubst_preserves_typing_tac2; constructor; listctx_set_solver);
  try (auto_exists_L; simpl; intros; msubst_preserves_typing_tac).
  - assert (forall x v, ctxfind Γv x = Some v -> closed_value v). eapply instantiation_regular_closed; eauto.
    rewrite ctxfind_app in e; auto. destruct e.
    + eapply instantiation_R_exists in H0; eauto. destruct H0 as (v & Hv1 & Hv2 & Hv3).
      erewrite msubst_var; eauto. basic_typing_solver2.
    + rewrite msubst_var_none; basic_typing_solver2.
      apply instantiation_regular_ok in H0. repeat destruct_hyp_conj. rewrite <- H0.
      apply ctxfind_app_exclude in o. my_set_solver.
  - (* auto_exists_L; simpl; intros. repeat specialize_with f. *)
    msubst_preserves_typing_tac.
    specialize (H Γt (Γt' ++ [(f, TBase Tx)]) Γv).
    rewrite msubst_vlam in H.
    rewrite msubst_open_tm; try instantiation_regular_solver. apply H; auto.
    rewrite app_assoc; auto.
Qed.

Lemma msubst_preserves_typing_value: ∀ Γ Γv e T,
    Γ ⊢t e ⋮v T -> instantiation Γ Γv -> [] ⊢t (value_msubst Γv e) ⋮v T.
Proof.
  intros. eapply msubst_preserves_typing_value_aux; eauto. listctx_set_simpl.
Qed.

Definition termRraw Γ e e' :=
forall env (v: value), instantiation Γ env ->
                  (tm_msubst env e) ↪* v -> (tm_msubst env e') ↪* v.

Global Hint Unfold termRraw: core.

Inductive termR: listctx ty -> ty -> tm -> tm -> Prop :=
| termR_c: forall Γ T (e e': tm),
    Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T -> termRraw Γ e e' -> termR Γ T e e'.

Notation " e1 '<-<{' Γ ';' T '}' e2 " := (termR Γ T e1 e2) (at level 10).
Notation " e1 '>=<{' Γ ';' T '}' e2 " := (termR Γ T e1 e2 /\ termR Γ T e2 e1) (at level 10).

Global Hint Constructors termR: core.

Lemma termR_refl: forall Γ T e, Γ ⊢t e ⋮t T -> termR Γ T e e.
Proof.
  intros. constructor; auto.
Qed.

Lemma termR_trans: forall Γ T e1 e2 e3, Γ ⊢t e1 ⋮t T -> Γ ⊢t e2 ⋮t T -> Γ ⊢t e3 ⋮t T ->
                                   termR Γ T e1 e2 -> termR Γ T e2 e3 -> termR Γ T e1 e3.
Proof.
  intros. invclear H2. invclear H3. constructor; auto.
Qed.

Lemma termRraw_emp: forall e e' T,
    [] ⊢t e ⋮t T -> [] ⊢t e' ⋮t T ->
    termRraw [] e e' -> (forall (v: value), e ↪* v -> e' ↪* v).
Proof.
  intros. unfold termRraw in H1. specialize (H1 [] v).
  rewrite tm_msubst_closed in H1; basic_typing_solver3.
Qed.

Definition value_inhabitant_oracle (T: ty) : value :=
  match T with
  | TBool => false
  | TNat => 0
  | T1 ⤍ T2 => vlam T1 terr
  end.

Lemma value_inhabitant_oracle_spec: forall Γ T, ok Γ -> Γ ⊢t value_inhabitant_oracle T ⋮v T.
Proof.
  intros. destruct T.
  - destruct b; constructor; auto.
  - auto_exists_L.
Qed.

Lemma value_inhabitant_oracle_spec_empty: forall T, [] ⊢t value_inhabitant_oracle T ⋮v T.
Proof.
  intros. apply value_inhabitant_oracle_spec; auto.
Qed.

Global Hint Resolve value_inhabitant_oracle_spec_empty: core.

Lemma instantiation_msubst_perserve_ty: forall Γ env e T,
    instantiation Γ env -> Γ ⊢t e ⋮t T -> [] ⊢t (tm_msubst env e) ⋮t T.
Proof.
  induction Γ; intros; invclear H; auto.
  simpl. apply IHΓ; auto. basic_typing_solver3.
Qed.

Lemma termR_tlete_dummy: forall Γ Tx T (e_x e: tm), Γ ⊢t e_x ⋮t Tx -> Γ ⊢t e ⋮t T -> (tlete e_x e) <-<{Γ;T} e.
Proof.
  intros. constructor; auto.
  - basic_typing_solver.
  - unfold termRraw. intros. msubst_simpl.
    rewrite lete_step_spec in H2; mydestr.
    eapply instantiation_msubst_perserve_ty in H1; eauto.
    lc_simpl.
Qed.

Ltac mk_app_perserve_termR_tac :=
  match goal with
  | [H: ?e ↪* (tvalue ?v),
        H': ∀ v1 : value, ?e ↪* (tvalue v1) → ?e' ↪* (tvalue v1) |-
                            exists v_x: value, ?e' ↪* (tvalue v_x) /\ _ ] => exists v; split; auto
  end.

Ltac termR_solver1 :=
  intros; auto;
  repeat match goal with
    | [H: ?e <-<{_;_} ?e' |- ?Γ ⊢t ?e' ⋮t _ ] => invclear H; mydestr; eauto
    | [H: ?e <-<{_;_} ?e' |- ?Γ ⊢t ?e ⋮t _ ] => invclear H; mydestr; eauto
    | [H: ?e <-<{_;_} ?e' |- ?e' ↪* _ ] => invclear H; mydestr; eauto
    | [ |- ?e <-<{_;_} ?e] => constructor; eauto
    | [H: termRraw [] ?e ?e' |- ?e' ↪* _ ] =>
        apply termRraw_emp in H; try basic_typing_solver3; eauto
    end.

Lemma instantiation_implies_open_msubst:
      ∀ Γ Γv, instantiation Γ Γv -> forall e T Tu k (u: value),
          Γ ⊢t e ⋮t T -> [] ⊢t u ⋮v Tu ->
                {k ~t> u} (tm_msubst Γv e) = tm_msubst Γv ({k ~t> u} e).
Proof.
  intros Γ Γv Hi. induction Hi; simpl; intros; auto.
  rewrite IHHi with (T:=T0) (Tu:=Tu); eauto.
  - rewrite -> subst_open_tm; basic_typing_solver3.
    rewrite subst_fresh_value; basic_typing_solver3.
  - basic_typing_solver3.
Qed.

Lemma instantiation_implies_close_msubst:
  ∀ Γ Γv, instantiation Γ Γv ->
                    forall e k (x: atom), x ∉ ctxdom Γ -> {k <t~ x} (tm_msubst Γv e) = tm_msubst Γv ({k <t~ x} e).
Proof.
  intros Γ Γv Hi. induction Hi; simpl; intros; auto.
  rewrite IHHi; try fast_set_solver.
  - rewrite -> subst_close_tm; basic_typing_solver3.
Qed.

Lemma instantiation_implies_msubst_lc:
      ∀ Γ Γv, instantiation Γ Γv -> forall e, lc e -> lc (tm_msubst Γv e).
Proof.
  intros Γ Γv Hi. induction Hi; simpl; intros; auto.
  - apply IHHi. apply subst_lc_tm; basic_typing_solver3.
Qed.

Lemma mk_app_perserve_termR: forall Γ Tx T(e1 e2 e1' e2': tm),
    e1 <-<{Γ;Tx ⤍ T} e1' -> e2 <-<{Γ;Tx} e2' -> (mk_app e1 e2) <-<{Γ;T} (mk_app e1' e2').
Proof.
  intros.
  constructor; auto.
  - eapply mk_app_typable; termR_solver1.
  - eapply mk_app_typable; termR_solver1.
  - intros. invclear H. invclear H0. unfold mk_app; intros; mydestr.
    unfold termRraw; intros. msubst_simpl.
    rewrite lete_step_spec in H6; simpl; mydestr. rewrite lete_step_spec; simpl.
    split.
    + unfold body in H0; mydestr. auto_exists_L; intros. lc_simpl.
      simpl in H8.
      assert (lc e2') as He2' by basic_typing_solver3.
      eapply instantiation_implies_msubst_lc in He2'; eauto.
      rewrite open_rec_lc_tm; basic_typing_solver3.
    + apply H3 in H7; auto. exists x. split; auto. lc_simpl.
      assert ([] ⊢t x ⋮v Tx ⤍ T).
      { eapply instantiation_msubst_perserve_ty in H2; eauto.
        basic_typing_solver3. }
      simpl in H8.
      erewrite instantiation_implies_open_msubst; eauto.
      erewrite instantiation_implies_open_msubst in H8; eauto.
      lc_simpl.
      rewrite lete_step_spec in H8; simpl; mydestr.
      rewrite lete_step_spec; simpl. split; auto.
      eexists; split; eauto.
Qed.

Lemma tyable_implies_terr_termR: forall (e: tm) Γ T, Γ ⊢t e ⋮t T -> terr <-<{ Γ; T} e.
Proof.
  intros. repeat split; auto.
  - constructor; basic_typing_solver2.
  - econstructor; eauto. msubst_simpl. auto_reduction_exfalso.
Qed.

Lemma tyable_implies_terr_termR_terr: forall (e: tm) Γ T1 T, Γ ⊢t e ⋮t T1 -> tlete e terr <-<{ Γ; T} terr.
Proof.
  intros. repeat split; auto.
  - auto_exists_L. intros. simpl. constructor. basic_typing_solver.
  - econstructor; basic_typing_solver.
  - econstructor; eauto. msubst_simpl. auto_reduction_exfalso.
Qed.

Lemma msubst_subst_commute_tm: forall Γ Γv,
    instantiation Γ Γv ->
    forall x u e, x ∉ ctxdom Γv -> closed_value u ->
             {x := u }t tm_msubst Γv e = tm_msubst Γv ({x := u }t e).
Proof.
  intros Γv Γ Hi; induction Hi; simpl; intros; mydestr; auto.
  rewrite IHHi; try fast_set_solver.
  rewrite subst_commute_tm; auto; basic_typing_solver3; set_solver.
Qed.

Lemma msubst_subst_commute_value: forall Γ Γv,
    instantiation Γ Γv ->
    forall x u e, x ∉ ctxdom Γv -> closed_value u ->
             {x := u }v value_msubst Γv e = value_msubst Γv ({x := u }v e).
Proof.
  intros Γv Γ Hi; induction Hi; simpl; intros; mydestr; auto.
  rewrite IHHi; try fast_set_solver.
  rewrite subst_commute_value; auto; basic_typing_solver3; set_solver.
Qed.

Lemma tm_msubst_mid_subst: forall Γv1 x u Γv2 Γ,
    instantiation Γ (Γv1 ++ (x, u) :: Γv2) -> closed_value u ->
    ∀ e, tm_msubst (Γv1 ++ (x, u) :: Γv2) e = tm_msubst (Γv1 ++ Γv2) ({x:= u}t e).
Proof.
  induction Γv1; simpl; intros; mydestr; auto.
  invclear H.
  erewrite IHΓv1; eauto. apply instantiation_regular in H7; mydestr. listctx_set_simpl.
  rewrite subst_commute_tm; auto; basic_typing_solver3; set_solver.
Qed.

Lemma value_msubst_mid_subst: forall Γv1 x u Γv2 Γ,
    instantiation Γ (Γv1 ++ (x, u) :: Γv2) -> closed_value u ->
    ∀ e, value_msubst (Γv1 ++ (x, u) :: Γv2) e = value_msubst (Γv1 ++ Γv2) ({x:= u}v e).
Proof.
  induction Γv1; simpl; intros; mydestr; auto.
  invclear H.
  erewrite IHΓv1; eauto. apply instantiation_regular in H7; mydestr. listctx_set_simpl.
  rewrite subst_commute_value; auto; basic_typing_solver3; set_solver.
Qed.

Lemma instantiation_app_spec: forall Γv1 Γv2 Γ,
    instantiation Γ (Γv1 ++ Γv2) <->
      ∃ Γ1 Γ2, Γ = Γ1 ++ Γ2 /\ ok Γ /\ instantiation Γ1 Γv1 /\ instantiation Γ2 Γv2 .
Proof.
  induction Γv1; split; simpl; intros.
  - exists [], Γ. repeat split; simpl; auto; instantiation_regular_solver.
  - mydestr; subst. invclear H1. auto.
  - invclear H. apply IHΓv1 in H5; mydestr.
    exists ((x, T) :: x0), x1. subst. repeat split; auto.
    + rewrite ok_pre_destruct; split; auto.
    + constructor; listctx_set_solver.
  - mydestr; subst. invclear H1. listctx_set_simpl.
    constructor; auto; listctx_set_simpl.
    rewrite IHΓv1. exists c, x0. repeat split; auto.
Qed.

Ltac instantiation_regular_simp :=
  repeat match goal with
    | [H: instantiation _ _ |- _ ∉ _ ] => apply instantiation_regular in H; mydestr
    end.

Lemma instantiation_app_spec': forall Γ1 Γ2 Γv,
    instantiation (Γ1 ++ Γ2) Γv <->
      ∃ Γv1 Γv2, Γv = Γv1 ++ Γv2 /\ ok Γv /\ instantiation Γ1 Γv1 /\ instantiation Γ2 Γv2 .
Proof.
  induction Γ1; split; simpl; intros.
  - exists [], Γv. repeat split; simpl; auto; instantiation_regular_solver.
  - mydestr; subst. invclear H1. auto.
  - invclear H. apply IHΓ1 in H5; mydestr.
    exists ((x, v) :: x0), x1. subst. repeat split; auto.
    + rewrite ok_pre_destruct; split; auto.
      instantiation_regular_simp. listctx_set_simpl. set_solver.
    + constructor; listctx_set_solver.
  - mydestr; subst. invclear H1. listctx_set_simpl.
    constructor; auto; listctx_set_simpl. instantiation_regular_simp. set_solver.
    rewrite IHΓ1. exists e, x0. repeat split; auto.
Qed.

Lemma tm_msubst_swap_hd_tl: forall Γv Γ Γv',
    instantiation Γ (Γv ++ Γv') -> ∀ e, tm_msubst (Γv ++ Γv') e = tm_msubst (Γv' ++ Γv) e.
Proof.
  induction Γv; intros.
  - listctx_set_simpl.
  - invclear H. rewrite instantiation_app_spec in H5; mydestr; subst.
    listctx_set_simpl. simpl.
    rewrite IHΓv with (Γ := (x0 ++ x1)); auto.
    rewrite tm_msubst_mid_subst with (Γ := (x1 ++ (x, T) :: x0)); eauto.
    + rewrite instantiation_app_spec. exists x1, ((x, T) :: x0). repeat split; auto.
      apply ok_mid_insert; split; listctx_set_solver5.
      constructor; auto; listctx_set_solver5.
    + basic_typing_solver3.
    + rewrite instantiation_app_spec. exists x0, x1. split; auto.
Qed.

Lemma msubst_preserves_body_tm: forall Γ Γv e,
    instantiation Γ Γv -> body e -> body (tm_msubst Γv e).
Proof.
  intros. induction H; simpl; auto.
  erewrite <- msubst_subst_commute_tm; eauto.
  apply subst_body_tm; auto; basic_typing_solver3.
  - instantiation_regular_solver.
  - basic_typing_solver3.
Qed.

Lemma termRraw_swap: forall e e' Γ1 Γ2, termRraw (Γ1 ++ Γ2) e e' -> termRraw (Γ2 ++ Γ1) e e'.
Proof.
  unfold termRraw. intros.
  apply instantiation_app_spec' in H0; mydestr; subst.
  assert (instantiation (Γ2 ++ Γ1) (x ++ x0)).
  { apply instantiation_app_spec'. exists x, x0. repeat split; auto. }
  erewrite tm_msubst_swap_hd_tl; eauto.
  erewrite tm_msubst_swap_hd_tl in H1; eauto.
  apply H; auto.
  rewrite instantiation_app_spec'. exists x0, x. repeat split; auto.
  listctx_set_solver5.
Qed.

Lemma termR_swap: forall e e' Γ1 Γ2 T, e <-<{ Γ1 ++ Γ2; T} e' <-> e <-<{ Γ2 ++ Γ1; T} e'.
Proof.
  split; intros; invclear H; constructor; auto; basic_typing_solver4; apply termRraw_swap; auto.
Qed.

Lemma termR_elete: forall γ Tx T e_x e_x' e e' (x: atom),
    e_x <-<{γ; Tx} e_x' -> e <-<{γ ++ [(x, Tx)]; T} e' ->
    (tlete e_x (x \t\ e)) <-<{γ; T} (tlete e_x' (x \t\ e')).
Proof.
    intros.
    assert (ok (γ ++ [(x, Tx)])) as HH. invclear H0. basic_typing_solver.
    invclear H. invclear H0. repeat split; auto.
  - auto_exists_L; intros. rewrite subst_as_close_open_tm; try basic_typing_solver.
    apply basic_has_type_renaming; eauto;  basic_typing_solver3.
  - auto_exists_L; intros. rewrite subst_as_close_open_tm; try basic_typing_solver.
    apply basic_has_type_renaming; eauto;  basic_typing_solver3.
  - unfold termRraw. intros Γv u Hi. intros. msubst_simpl.
    rewrite lete_step_spec in H0; simpl; mydestr.
    rewrite lete_step_spec; simpl.
    split.
    { eapply msubst_preserves_body_tm; eauto.
      auto_exists_L; intros. rewrite subst_as_close_open_tm; try basic_typing_solver3.
      apply subst_lc_tm; auto. }
    exists x0. split; auto.
    setoid_rewrite <- instantiation_implies_close_msubst in H7; eauto; basic_typing_solver3.
    setoid_rewrite <- instantiation_implies_close_msubst; eauto; basic_typing_solver3.
    setoid_rewrite subst_as_close_open_tm in H7; basic_typing_solver3.
    setoid_rewrite subst_as_close_open_tm; basic_typing_solver3.
    + specialize (H5 (Γv ++ [(x, x0)]) u).
      assert ([] ⊢t (tm_msubst Γv e_x ) ⋮t Tx) by (eapply msubst_preserves_typing_tm; eauto).
      assert ([] ⊢t x0 ⋮v Tx) by basic_typing_solver3.
      assert (instantiation (γ ++ [(x, Tx)]) (Γv ++ [(x, x0)])).
      { rewrite instantiation_app_spec. exists γ, [(x, Tx)]; repeat split; auto.
        repeat constructor; auto; try fast_set_solver. }
      rewrite tm_msubst_swap_hd_tl with (Γ := (γ ++ [(x, Tx)])) in H5; auto; simpl in H5.
      rewrite tm_msubst_swap_hd_tl with (Γ := (γ ++ [(x, Tx)])) in H5; auto; simpl in H5.
      rewrite <- msubst_subst_commute_tm with (Γ := γ) in H5; auto; basic_typing_solver3; try instantiation_regular_solver.
      rewrite <- msubst_subst_commute_tm with (Γ := γ) in H5; auto; basic_typing_solver3; try instantiation_regular_solver.
    + eapply instantiation_implies_msubst_lc; eauto.
    + eapply instantiation_implies_msubst_lc; eauto.
Qed.

Lemma tm_msubst_then_subst: forall Γ env,
    instantiation Γ env ->
    forall (z: atom) (u: value) e, z ∉ ctxdom env -> z # u ->
    tm_msubst env ({z := u }t e) = ({z := value_msubst env u }t (tm_msubst env e)).
Proof.
  intros Γ env Hi. unfold closed_value.
  induction Hi; simpl; intros; mydestr; auto.
  - setoid_rewrite subst_subst_tm; try basic_typing_solver.
    rewrite IHHi; try fast_set_solver. simpl.
    apply basic_typing_contains_fv_value in H.
    pose (fv_of_subst_value x v u). set_solver.
Qed.

Lemma value_msubst_then_subst: forall Γ env,
    instantiation Γ env ->
    forall (z: atom) (u: value) e, z ∉ ctxdom env -> z # u ->
    value_msubst env ({z := u }v e) = ({z := value_msubst env u }v (value_msubst env e)).
Proof.
  intros Γ env Hi. unfold closed_value.
  induction Hi; simpl; intros; mydestr; auto.
  - setoid_rewrite subst_subst_value; try basic_typing_solver.
    rewrite IHHi; try fast_set_solver.
    apply basic_typing_contains_fv_value in H.
    pose (fv_of_subst_value x v u). set_solver.
Qed.

Lemma tm_msubst_then_open: forall Γ env,
    instantiation Γ env ->
    forall k (u: value) e, ctxdom env ∩ fv_value u = ∅ ->
                    {k ~t> u} (tm_msubst env e) = (tm_msubst env ({k ~t> u} e)).
Proof.
  intros Γ env Hi.
  induction Hi; simpl; intros; mydestr; auto.
  - setoid_rewrite subst_open_tm; try basic_typing_solver.
    rewrite (subst_fresh_value u).
    rewrite IHHi; auto; set_solver.
    set_solver.
Qed.

Lemma value_msubst_then_open: forall Γ env,
    instantiation Γ env ->
    forall k (u: value) e, ctxdom env ∩ fv_value u = ∅ ->
                    {k ~v> u} (value_msubst env e) = (value_msubst env ({k ~v> u} e)).
Proof.
  intros Γ env Hi.
  induction Hi; simpl; intros; mydestr; auto.
  - setoid_rewrite subst_open_value; try basic_typing_solver.
    rewrite (subst_fresh_value u).
    rewrite IHHi; auto; set_solver.
    set_solver.
Qed.

Lemma tm_msubst_then_open_closed: forall Γ env,
    instantiation Γ env ->
    forall k (u: value) e, fv_value u ≡ ∅ ->
                    {k ~t> u} (tm_msubst env e) = (tm_msubst env ( {k ~t> u} e)).
Proof.
  intros. eapply tm_msubst_then_open; eauto. set_solver.
Qed.

Lemma value_msubst_then_open_closed: forall Γ env,
    instantiation Γ env ->
    forall k (u: value) e, fv_value u ≡ ∅ ->
                    {k ~v> u} (value_msubst env e) = (value_msubst env ({k ~v> u} e)).
Proof.
   intros. eapply value_msubst_then_open; eauto. set_solver.
Qed.

Lemma instantiation_implies_tm_msubst_closed:
  forall Γ env, instantiation Γ env -> ∀ e T, Γ ⊢t e ⋮t T -> closed_tm (tm_msubst env e).
Proof.
  intros Γ env Hi. induction Hi; simpl; intros; basic_typing_solver5.
  assert (c ⊢t ({x := v }t e0) ⋮t T0) by basic_typing_solver5; eauto.
Qed.

Lemma instantiation_implies_value_msubst_closed:
  forall Γ env, instantiation Γ env -> ∀ (e: value) T, Γ ⊢t e ⋮v T -> closed_value (value_msubst env e).
Proof.
  intros Γ env Hi. induction Hi; simpl; intros; basic_typing_solver5.
  assert (c ⊢t ({x := v }v e0) ⋮v T0) by basic_typing_solver5; eauto.
Qed.

Global Hint Unfold closed_value: core.
Global Hint Unfold closed_tm: core.

Ltac isolver :=
  instantiation_regular_solver || (basic_typing_solver5; lc_solver1).

Lemma tlete_reduce_to_subst: forall (u: value) z e,
    lc u -> lc e ->
    tlete u (z \t\ e) ↪* {z := u }t e.
Proof.
  intros.
  apply multistep_trans with (y := (z \t\ e) ^t^ u).
  apply multistep_R. econstructor; isolver.
  setoid_rewrite subst_as_close_open_tm; eauto.
  apply subst_lc_tm; auto.
  setoid_rewrite subst_as_close_open_tm; eauto.
  eapply multistep_refl. apply subst_lc_tm; auto; isolver.
Qed.

Lemma value_reduce_to_value_implies_same: forall (v1 v2: value), v1 ↪* v2 <-> v1 = v2 /\ lc v2.
Proof.
  split; intros.
  - invclear H; auto. invclear H0.
  - mydestr; subst. apply multistep_refl; auto.
Qed.

Lemma termR_let_one_step_from_basic_type: forall Γ (u: value) (z: atom) e T,
    lc e -> z ∉ ctxdom Γ ->
    Γ ⊢t (tlete u (z \t\ e)) ⋮t T ->
    (tlete u (z \t\ e)) <-<{ Γ; T} ({z := u }t e).
Proof.
  intros. constructor; auto.
  - eapply multi_preservation; eauto.
    apply tlete_reduce_to_subst; isolver.
  - unfold termRraw. intros. msubst_simpl.
    rewrite lete_step_spec in H3; simpl; mydestr.
    rewrite value_reduce_to_value_implies_same in H4; mydestr; subst.
    invclear H1.
    assert (closed_value (value_msubst env0 u)) by
    (eapply instantiation_implies_value_msubst_closed; eauto; basic_typing_solver5).
    assert (z ∉ ctxdom env0) by instantiation_regular_solver.
    erewrite tm_msubst_then_subst; eauto; try basic_typing_solver5.
    erewrite tm_msubst_then_open_closed in H5; eauto; try basic_typing_solver5.
    rewrite subst_as_close_open_tm in H5; eauto; try basic_typing_solver5.
    erewrite tm_msubst_then_subst in H5; eauto; try basic_typing_solver5.
    eapply value_msubst_closed in H1. rewrite H1 in H5; auto.
    set_solver.
Qed.

Lemma instantiation_implies_value_msubst_lc:
      ∀ Γ Γv, instantiation Γ Γv -> forall (e: value), lc e -> lc (value_msubst Γv e).
Proof.
  intros Γ Γv Hi. induction Hi; simpl; intros; auto.
  - apply IHHi. apply subst_lc_value; basic_typing_solver3.
Qed.

Lemma termR_let_one_step_from_basic_type': forall Γ (u: value) (z: atom) e T,
    lc e -> z ∉ ctxdom Γ ->
    Γ ⊢t (tlete u (z \t\ e)) ⋮t T ->
    ({z := u }t e) <-<{ Γ; T} (tlete u (z \t\ e)).
Proof.
  intros. constructor; auto.
  - eapply multi_preservation; eauto.
    apply tlete_reduce_to_subst; isolver.
  - unfold termRraw. intros. msubst_simpl.
    rewrite lete_step_spec. split.
    + eapply msubst_preserves_body_tm; eauto. lc_solver.
      setoid_rewrite subst_as_close_open_tm; eauto.
      apply subst_lc_tm; auto.
    + invclear H1.
      exists (value_msubst env0 u). split.
      { rewrite value_reduce_to_value_implies_same; split; auto.
        eapply instantiation_implies_value_msubst_lc; eauto. basic_typing_solver5. }
      assert (z ∉ ctxdom env0) by instantiation_regular_solver.
      assert (closed_value (value_msubst env0 u)) by
        (eapply instantiation_implies_value_msubst_closed; eauto; basic_typing_solver5).
      erewrite tm_msubst_then_subst in H3; eauto; try basic_typing_solver5.
      erewrite tm_msubst_then_open_closed; eauto; try basic_typing_solver5.
      rewrite subst_as_close_open_tm; eauto; try basic_typing_solver5.
      erewrite tm_msubst_then_subst; eauto; try basic_typing_solver5.
      rewrite value_msubst_closed; auto.
      set_solver.
Qed.

Lemma termR_tm_subst: forall γ Tx T (v_x: value) e e' (x: atom),
    [] ⊢t v_x ⋮v Tx ->
    e <-<{γ ++ [(x, Tx)]; T} e' ->
    ({x := v_x}t e) <-<{γ; T} ({x := v_x}t e').
Proof.
    intros.
    assert (ok (γ ++ [(x, Tx)])) as HH. invclear H0. basic_typing_solver.
    invclear H0. repeat split; auto.
  - assert (γ ⊢t v_x ⋮v Tx) by basic_typing_solver3.
    eapply basic_typing_subst_tm_pre in H0; basic_typing_solver3.
  - assert (γ ⊢t v_x ⋮v Tx) by basic_typing_solver3.
    eapply basic_typing_subst_tm_pre in H0; basic_typing_solver3.
  - unfold termRraw. intros Γv u Hi. intros. msubst_simpl.
    unfold termRraw in H3.
    specialize (H3 (Γv ++ [(x, v_x)]) u).
    assert (instantiation (γ ++ [(x, Tx)]) (Γv ++ [(x, v_x )])).
    { rewrite instantiation_app_spec. exists γ, [(x, Tx)]; repeat split; auto.
        repeat constructor; auto; try fast_set_solver. }
    assert (tm_msubst (Γv ++ [(x, v_x)]) e ↪* u); auto.
    rewrite tm_msubst_swap_hd_tl with (Γ := (γ ++ [(x, Tx)])); auto.
    apply H3 in H5; auto.
    rewrite tm_msubst_swap_hd_tl with (Γ := (γ ++ [(x, Tx)])) in H5; auto.
Qed.

Lemma termR_value_iff_same: forall (v v': value) T,
  v <-<{ []; T} v' <-> (v = v' /\ [] ⊢t v ⋮v T).
Proof.
  split; intros.
  - invclear H. split; basic_typing_solver. unfold termRraw in H2.
    assert (instantiation [] []); auto.
    apply (H2 _ v) in H. simpl in H.
    rewrite value_reduce_to_value_implies_same in H; mydestr; subst; auto.
    simpl. apply multistep_refl; auto. basic_typing_solver.
  - mydestr; subst; auto.
Qed.

Lemma value_msubst_swap_hd_tl: forall Γv Γ Γv',
    instantiation Γ (Γv ++ Γv') ->
    ∀ e, value_msubst (Γv ++ Γv') e = value_msubst (Γv' ++ Γv) e.
Proof.
  induction Γv; intros.
  - listctx_set_simpl.
  - invclear H. rewrite instantiation_app_spec in H5; mydestr; subst.
    listctx_set_simpl. simpl.
    rewrite IHΓv with (Γ := (x0 ++ x1)); auto.
    rewrite value_msubst_mid_subst with (Γ := (x1 ++ (x, T) :: x0)); eauto.
    + rewrite instantiation_app_spec. exists x1, ((x, T) :: x0). repeat split; auto.
      apply ok_mid_insert; split; listctx_set_solver5.
      constructor; auto; listctx_set_solver5.
    + basic_typing_solver3.
    + rewrite instantiation_app_spec. exists x0, x1. split; auto.
Qed.

Lemma termR_value_subst: forall γ Tx T (v_x: value) (e e': value) (x: atom),
    [] ⊢t v_x ⋮v Tx ->
    e <-<{γ ++ [(x, Tx)]; T} e' ->
    ({x := v_x}v e) <-<{γ; T} ({x := v_x}v e').
Proof.
    intros.
    assert (ok (γ ++ [(x, Tx)])) as HH. invclear H0. basic_typing_solver.
    invclear H0. repeat split; auto.
  - assert (γ ⊢t v_x ⋮v Tx) by basic_typing_solver3.
    eapply basic_typing_subst_tm_pre in H1; basic_typing_solver3.
  - assert (γ ⊢t v_x ⋮v Tx) by basic_typing_solver3.
    eapply basic_typing_subst_tm_pre in H2; basic_typing_solver3.
  - unfold termRraw. intros Γv u Hi. intros. msubst_simpl.
    unfold termRraw in H3.
    specialize (H3 (Γv ++ [(x, v_x)]) u).
    assert (instantiation (γ ++ [(x, Tx)]) (Γv ++ [(x, v_x )])).
    { rewrite instantiation_app_spec. exists γ, [(x, Tx)]; repeat split; auto.
        repeat constructor; auto; try fast_set_solver. }
    msubst_simpl; auto.
    assert (tm_msubst (Γv ++ [(x, v_x)]) e ↪* u); auto.
    rewrite tm_msubst_swap_hd_tl with (Γ := (γ ++ [(x, Tx)])); auto.
    simpl; auto. msubst_simpl; auto.
    assert (value_msubst (Γv ++ [(x, v_x)]) e' ↪* u).
    { apply H3 in H4; auto. msubst_simpl; auto. }
    rewrite value_msubst_swap_hd_tl with (Γ := (γ ++ [(x, Tx)])) in H6; auto.
Qed.

Lemma tm_open_then_msubst: forall Γ env,
    instantiation Γ env ->
    (forall e v, tm_msubst env (e ^t^ v) = (tm_msubst env e ^t^ value_msubst env v)).
Proof.
  intros Γ env Hi; induction Hi; simpl; intros; auto.
  rewrite subst_open_tm; basic_typing_solver6.
Qed.

Lemma value_open_then_msubst: forall Γ env,
    instantiation Γ env ->
    (forall e v, value_msubst env (e ^v^ v) = (value_msubst env e ^v^ value_msubst env v)).
Proof.
  intros Γ env Hi; induction Hi; simpl; intros; auto.
  rewrite subst_open_value; basic_typing_solver6.
Qed.

Ltac lc_solver3 :=
  lc_solver ||
  match goal with
  | [|- lc (tvalue (value_msubst _ _))] =>
      eapply instantiation_implies_value_msubst_lc; eauto;
      basic_typing_solver
  end.

Ltac reduction_simpl1 :=
  repeat ((simpl; lc_simpl; msubst_simpl) ||
            match goal with
            | [H: (tvalue _) ↪* (tvalue _) |- _ ] =>
                rewrite value_reduce_to_value_implies_same in H; mydestr; subst
            | [|- (tvalue _) ↪* (tvalue _)] =>
                rewrite value_reduce_to_value_implies_same; split; eauto
            | [H: context [?e ^v^ _] |- _ ] =>
                assert (lc e) as Htmp by (auto; lc_solver3);
                rewrite (open_rec_lc_value _ e) in H; auto;
                try clear Htmp
            | [|- context [?e ^v^ _] ] =>
                assert (lc e) as Htmp by (auto; lc_solver3);
                rewrite (open_rec_lc_value _ e); auto;
                try clear Htmp
            | [H: context [?e ^t^ _] |- _ ] =>
                assert (lc e) as Htmp by (auto; lc_solver3);
                rewrite (open_rec_lc_tm _ e) in H; auto;
                try clear Htmp
            | [|- context [?e ^t^ _] ] =>
                assert (lc e) as Htmp by (auto; lc_solver3);
                rewrite (open_rec_lc_tm _ e); auto;
                try clear Htmp
            end || auto_reduction_exfalso).

Lemma mk_app_reduce_to_open:
  ∀ (Γ : listctx ty) (Tx T : ty) e1 (v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vlam Tx e1) ⋮v (Tx ⤍ T) ->
    (mk_app (vlam Tx e1) v2) <-<{ Γ; T} (e1 ^t^ v2).
Proof.
  intros. constructor.
  - eapply mk_app_typable; eauto.
  - basic_typing_solver6.
  - unfold termRraw. intros. unfold mk_app in H2. reduction_simpl1.
    rewrite lete_step_spec in H2; simpl; mydestr. simpl in H4.
    rewrite lete_step_spec in H4; simpl; mydestr. simpl in H6.
    reduction_simpl1.
    rewrite letapp_step_spec in H6; mydestr.
    destruct H9; mydestr; invclear H9.
    rewrite lete_step_spec in H10; simpl; mydestr. simpl in H11.
    reduction_simpl1.
    erewrite tm_open_then_msubst; eauto.
Qed.

Lemma body_tm_open_1_same: forall e v, body e -> {1 ~t> v} e = e.
Proof.
  intros. invclear H. auto_pose_fv y. specialize_with y.
  apply fact1_tm with (j := 0) (v:=y); try lia.
  rewrite open_rec_lc_tm; auto.
Qed.

Lemma body_value_open_1_same: forall (e: value) v, body e -> {1 ~v> v} e = e.
Proof.
  intros. invclear H. auto_pose_fv y. specialize_with y.
  apply fact1_value with (j := 0) (v:=y); try lia.
  rewrite open_rec_lc_value; auto.
Qed.

Ltac op_solver1 :=
  op_simpl;
  auto;
  repeat match goal with
    | [H: _ ⊢t ?e ⋮t _ |- lc ?e ] => apply basic_typing_regular_tm in H; destruct H; auto
    | [H: _ ↪* ?e |- lc ?e] => apply multi_step_regular2 in H; auto
    | [H: ?Γ ⊢t ?e ⋮t ?T |- (?Γ ++ _) ⊢t ?e ⋮t _] => apply basic_typing_weaken_tm_pre; eauto
    | [H: ?Γ ⊢t _ ⋮t _ |- ok _ ] => apply basic_typing_regular_tm in H; destruct H
    end; listctx_set_solver.

Ltac reduction_solver1 :=
  reduction_simpl1; eauto;
  repeat (
      (match goal with
       | [|- lc (tvalue (value_msubst _ _))] =>
           eapply instantiation_implies_value_msubst_lc; eauto;
           basic_typing_solver6
       | [|- lc (tm_msubst _ _)] =>
           eapply instantiation_implies_msubst_lc; eauto;
           basic_typing_solver6
       | [|- lc (tvalue (value_msubst _ _))] =>
           eapply instantiation_implies_value_msubst_lc; eauto;
           basic_typing_solver
       end) || op_solver1 || basic_typing_solver6).

Global Hint Resolve mk_app_body: core.

Lemma mk_app_reduce_to_let':
  ∀ (Γ : listctx ty) (Tx T : ty) e1 e2,
    Γ ⊢t e2 ⋮t Tx -> Γ ⊢t (vlam Tx e1) ⋮v (Tx ⤍ T) ->
    (tlete e2 e1) <-<{ Γ; T} (mk_app (vlam Tx e1) e2).
Proof.
  intros. constructor; basic_typing_solver6.
  - invclear H0. auto_exists_L; simpl; intros.
  - eapply mk_app_typable; eauto.
  - unfold termRraw. intros. unfold mk_app. reduction_simpl1.
    assert (lc (tm_msubst env0 e2)) by reduction_solver1.
    assert (lc (value_msubst env0 (vlam Tx e1))) by
      (eapply instantiation_implies_value_msubst_lc; eauto; basic_typing_solver6).
    rewrite lete_step_spec. split; auto.
    eexists; split; reduction_simpl1.
    rewrite lete_step_spec. split; auto.
    rewrite lete_step_spec in H2; mydestr; subst.
    eexists; split; eauto.
    simpl. rewrite body_tm_open_1_same; reduction_solver1.
    rewrite letapp_step_spec. repeat split; reduction_solver1.
    left. do 2 eexists. split; auto.
    rewrite lete_step_spec. split; eauto.
    eexists; split; reduction_solver1.
Qed.

Lemma mk_app_reduce_to_open':
  ∀ (Γ : listctx ty) (Tx T : ty) e1 (v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vlam Tx e1) ⋮v (Tx ⤍ T) ->
    (e1 ^t^ v2) <-<{ Γ; T} (mk_app (vlam Tx e1) v2).
Proof.
  intros. constructor; basic_typing_solver6.
  - eapply mk_app_typable; eauto.
  - unfold termRraw. intros. unfold mk_app. reduction_simpl1.
    assert (lc (value_msubst env0 v2)) by reduction_solver1.
    assert (lc (value_msubst env0 (vlam Tx e1))) by
      (eapply instantiation_implies_value_msubst_lc; eauto; basic_typing_solver6).
    rewrite lete_step_spec. split; auto.
    eexists; split; reduction_simpl1.
    rewrite lete_step_spec. split; auto.
    eexists; split; reduction_simpl1.
    simpl. rewrite body_tm_open_1_same; reduction_solver1.
    rewrite letapp_step_spec. repeat split; reduction_solver1.
    left. do 2 eexists. split; auto.
    rewrite lete_step_spec. split; auto.
    eexists; split; reduction_solver1.
    erewrite tm_open_then_msubst in H2; eauto.
Qed.

Lemma stuck_tm_termR_terr: forall e B T,
    (∀ e' : value, ¬ e ↪* e') -> [] ⊢t e ⋮t B ⤍ T -> e <-<{ []; B ⤍ T} terr.
Proof.
  intros. constructor; auto.
  unfold termRraw. intros. invclear H1. simpl in H2. exfalso. eapply H; eauto.
Qed.

Lemma let_value_in_lc_termR_drop: forall Γ (v_x: value) e Tx T,
    Γ ⊢t v_x ⋮v Tx -> Γ ⊢t e ⋮t T -> e <-<{ Γ; T} (tlete v_x e).
Proof.
  intros. constructor; auto.
  - auto_exists_L; intros. assert (lc e); reduction_solver1.
  - unfold termRraw; intros. reduction_simpl1.
    assert (lc (tm_msubst env0 e)) by reduction_solver1.
    rewrite lete_step_spec. split; reduction_solver1.
    eexists; split; reduction_solver1.
Qed.

Lemma termR_tlete_drop_halt_lhs: forall e_x Tx e T,
    [] ⊢t e_x ⋮t Tx -> [] ⊢t e ⋮t T -> (∃ v : value, e_x ↪* v) ->
    e <-<{ []; T} (tlete e_x e).
Proof.
  intros. constructor; auto; basic_typing_solver6.
  unfold termRraw. intros. invclear H2. simpl in H3. simpl.
  rewrite lete_step_spec. split; basic_typing_solver.
  mydestr. eexists; split; eauto; reduction_solver1.
Qed.

Lemma termR_tlete_drop_halt_lhs': forall e_x Tx x e T,
    [] ⊢t e_x ⋮t Tx -> [] ⊢t e ⋮t T -> (∃ v : value, e_x ↪* v) ->
    e <-<{ []; T} (tlete e_x (x \t\ e)).
Proof.
  intros. rewrite close_fresh_rec_tm; basic_typing_solver6.
  eapply termR_tlete_drop_halt_lhs; eauto.
  apply basic_typing_contains_fv_tm in H0; simpl in H0. set_solver.
Qed.

Lemma let_store_typable: forall Γ u Tu z e T,
    Γ ⊢t u ⋮t Tu -> (Γ ++ [(z, Tu)]) ⊢t e ⋮t T -> Γ ⊢t tlete u (z \t\ e) ⋮t T.
Proof.
  intros. auto_exists_L; intros.
  rewrite subst_as_close_open_tm; eauto; try basic_typing_solver.
  apply basic_has_type_renaming; try basic_typing_solver.
Qed.

Lemma termR_tlete_commute_tlete: forall Γ e1 T1 e2 T2 e T x1 x2,
    x1 <> x2 ->
    [] ⊢t e1 ⋮t T1 -> [] ⊢t e2 ⋮t T2 -> ((x1, T1) :: Γ ++ [(x2, T2)]) ⊢t e ⋮t T ->
    (tlete (tlete e1 (x1 \t\ e2)) (x2 \t\ tlete e1 (x1 \t\ e)))
      <-<{ Γ;T} (tlete e1 (x1 \t\ tlete e2 (x2 \t\ e))).
Proof.
  intros.
  assert (Γ ⊢t (tlete e1 (x1 \t\ tlete e2 (x2 \t\ e))) ⋮t T) as Hsecond.
  { eapply let_store_typable; eauto; basic_typing_solver.
    eapply let_store_typable; eauto. apply basic_typing_weaken_tm_pre; eauto; basic_typing_solver.
    rewrite <- app_assoc. rewrite basic_has_type_swap_tm; auto. }
  constructor; auto.
  - apply let_store_typable with (Tu:= T2); eauto; basic_typing_solver.
    apply let_store_typable with (Tu:= T1); eauto; basic_typing_solver.
    eapply let_store_typable; eauto; basic_typing_solver.
    rewrite basic_has_type_head_to_tail_tm in H2; listctx_set_simpl.
  - assert (closed_tm e1) as Hclosede1 by basic_typing_solver.
    assert (closed_tm e2) as Hclosede2 by basic_typing_solver.
    assert (forall x, x ∉ fv_tm e1) as He1. intros; basic_typing_solver; set_solver.
    assert (forall x, x ∉ fv_tm e2) as He2. intros; basic_typing_solver; set_solver.
    unfold termRraw. intros Γv v Hi HH.
    assert (lc (tm_msubst Γv (tlete e1 (x1 \t\ tlete e2 (x2 \t\ e))))) as Hss by
      (eapply instantiation_implies_msubst_lc; eauto; basic_typing_solver).
    reduction_simpl1.
    rewrite lete_step_spec in HH; mydestr. rewrite lete_step_spec in H4; mydestr.
    rewrite tm_msubst_closed in H6; auto.
    rewrite tm_msubst_closed in H7; auto. rewrite open_rec_lc_tm in H7; auto; basic_typing_solver.
    rewrite tm_msubst_closed; auto. rewrite tm_msubst_closed; auto.
    simpl in H5. rewrite close_fresh_rec_tm in H5; auto.
    assert ([] ⊢t x ⋮v T2) by reduction_solver1.
    assert (closed_value x) by basic_typing_solver.
    erewrite tm_msubst_then_open_closed in H5; eauto. simpl in H5.
    rewrite open_rec_lc_tm in H5; basic_typing_solver. rewrite subst_as_close_open_tm_ in H5.
    msubst_simpl.
    rewrite lete_step_spec in H5; mydestr.
    rewrite tm_msubst_closed in H10; auto.
    assert ([] ⊢t x3 ⋮v T1) by reduction_solver1.
    assert (closed_value x3) by basic_typing_solver.
    erewrite tm_msubst_then_open_closed in H11; eauto.
    rewrite <- subst_open_tm_closed in H11; basic_typing_solver.
    rewrite subst_as_close_open_tm in H11; basic_typing_solver.
    rewrite lete_step_spec.
    assert (body (tlete e2 (tm_msubst Γv ({1 <t~ x1} (x2 \t\ e))))) as Hsss.
    { rewrite lete_lc_body in Hss; mydestr. simpl in H15. msubst_simpl.
      rewrite close_fresh_rec_tm in H15; auto. rewrite tm_msubst_closed in H15; auto. }
    split; auto. exists x3; split; eauto.
    simpl. rewrite open_rec_lc_tm; basic_typing_solver.
    rewrite lete_step_spec. split.
    { erewrite tm_msubst_then_open_closed; eauto.
      rewrite subst_as_close_open_tm_.
      eapply msubst_preserves_body_tm; eauto.
      rewrite <- subst_close_tm. apply body_lc_after_close_tm. apply subst_lc_tm; auto; basic_typing_solver.
      set_solver. set_solver.
      rewrite body_tm_open_1_same; auto. apply body_lc_after_close_tm. basic_typing_solver.
    }
    eexists; split; eauto.
    erewrite tm_msubst_then_open_closed; eauto.
    rewrite subst_as_close_open_tm_.
    erewrite tm_msubst_then_open_closed; eauto.
    rewrite <- subst_open_tm_closed; basic_typing_solver.
    rewrite subst_as_close_open_tm; basic_typing_solver.
    rewrite subst_commute_tm; auto; set_solver.
    rewrite body_tm_open_1_same; auto. apply body_lc_after_close_tm. basic_typing_solver.
    rewrite body_tm_open_1_same; auto. apply body_lc_after_close_tm. basic_typing_solver.
Qed.

Ltac termR_solver :=
  repeat (match goal with
          | [H: termRraw [] ?e ?e' |- ?e' ↪* _ ] =>
              assert ((forall (v: value), e ↪* v -> e' ↪* v)); auto;
              eapply termRraw_emp; eauto; try basic_typing_solver3
          | [|- (mk_app _ _) <-<{ _; _} (mk_app _ _)] => eapply mk_app_perserve_termR; eauto
          | [H: ?e <-<{ ?a ++ ?b; ?T} ?e' |- ?e <-<{ ?b ++ ?a; ?T} ?e'] => rewrite termR_swap; eauto
          | [H: ?e <-<{ (?x, ?t) :: ?b; ?T} ?e' |- ?e <-<{ ?b ++ [(?x, ?t)]; ?T} ?e'] => rewrite termR_swap; eauto
          end || termR_solver1).

Ltac lc_simpl4 :=
  match goal with
  | [H: context [{?x := ?v }t ({_ ~t> (vfvar ?x)} ?e)] |- _ ] =>
      assert (x ∉ stale e) as Htmp by fast_set_solver;
      rewrite open_subst_same_tm in H; auto; try clear Htmp
  | [|- context [{?x := ?v }t ({_ ~t> (vfvar ?x)} ?e)]] =>
      assert (x ∉ stale e) as Htmp by fast_set_solver;
      rewrite open_subst_same_tm; auto; try clear Htmp
  | [H: context [{?x := ?v }v ({_ ~v> (vfvar ?x)} ?e)] |- _ ] =>
      assert (x ∉ stale e) as Htmp by fast_set_solver;
      rewrite open_subst_same_value in H; auto; try clear Htmp
  | [|- context [{?x := ?v }v ({_ ~v> (vfvar ?x)} ?e)]] =>
      assert (x ∉ stale e) as Htmp by fast_set_solver;
      rewrite open_subst_same_value; auto; try clear Htmp
  end.

Lemma tletapp_typable
     : ∀ Γ (v1 v2 : value) (e : tm) (x : atom) (T1 T2 T: ty),
         x ∉ fv_tm e -> Γ ⊢t v1 ⋮v (T2 ⤍ T1) -> Γ ⊢t v2 ⋮v T2
         → (Γ ++ [(x, T1)]) ⊢t e ^t^ x ⋮t T -> Γ ⊢t tletapp v1 v2 e ⋮t T.
Proof.
  intros. auto_exists_L; intros.
  apply basic_has_type_renaming with (x0:=x0) in H2; auto.
  lc_simpl4. fast_set_solver. basic_typing_solver.
Qed.

Ltac instantiation_simp :=
   repeat match goal with
    | [H: instantiation [] _ |- _ ] => invclear H
    | [H: context [tm_msubst [] _ ] |- _ ] => simpl in H
    | [|- context [tm_msubst [] _ ] ] => simpl
    end.

Lemma tm_open_then_msubst_k: forall Γ env,
    instantiation Γ env ->
    (forall e k v, tm_msubst env ({k ~t> v} e) = ({k ~t> (value_msubst env v)} (tm_msubst env e))).
Proof.
  intros Γ env Hi; induction Hi; simpl; intros; auto.
  rewrite subst_open_tm; basic_typing_solver6.
Qed.

Lemma mk_app_v_v_reduce_to_letapp:
  ∀ (Γ : listctx ty) (Tx T2 : ty) (v1 v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t v1 ⋮v (Tx ⤍ T2) ->
    (mk_app v1 v2) <-<{ Γ; T2} (tletapp v1 v2 (vbvar 0)).
Proof.
  intros. constructor.
  - eapply mk_app_typable; eauto.
  - auto_exists_L; simpl; intros. basic_typing_vfavr_solver.
  - unfold termRraw. intros Γv. intros. unfold mk_app in H2. reduction_simpl1.
    rewrite lete_step_spec in H2; simpl; mydestr. simpl in H4. reduction_simpl1.
    rewrite lete_step_spec in H4; simpl; mydestr. simpl in H6. reduction_simpl1.
Qed.

Lemma mk_app_v_v_reduce_to_letapp':
  ∀ (Γ : listctx ty) (Tx T2 : ty) (v1 v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t v1 ⋮v (Tx ⤍ T2) ->
    (tletapp v1 v2 (vbvar 0)) <-<{ Γ; T2} (mk_app v1 v2).
Proof.
  intros. constructor.
  - auto_exists_L; simpl; intros. basic_typing_vfavr_solver.
  - eapply mk_app_typable; eauto.
  - unfold termRraw. intros Γv. intros. unfold mk_app. reduction_simpl1.
    rewrite lete_step_spec. split; auto. apply mk_app_body. reduction_solver1.
    exists (value_msubst Γv v1). split; eauto. reduction_solver1.
    simpl. reduction_simpl1.
    rewrite lete_step_spec. split; auto. reduction_solver1. reduction_simpl1.
    exists (value_msubst Γv v2). split; eauto. reduction_solver1. reduction_simpl1.
Qed.

Lemma lete_0_reduce_to_self_aux: ∀ (Γ : listctx ty) e,
    termRraw Γ e (tlete e (vbvar 0)).
Proof.
  intros. unfold termRraw. intros Γv. intros. reduction_simpl1.
  rewrite lete_step_spec. split; auto. eexists; split; eauto. reduction_solver1.
Qed.

Lemma lete_0_reduce_to_self_aux': ∀ (Γ : listctx ty) e,
    termRraw Γ (tlete e (vbvar 0)) e.
Proof.
  intros. unfold termRraw. intros Γv. intros. reduction_simpl1.
  rewrite lete_step_spec in H0; mydestr. simpl in H2. reduction_simpl1; auto.
Qed.

Lemma lete_0_reduce_to_self: ∀ (Γ : listctx ty) (T : ty) e,
    Γ ⊢t e ⋮t T -> e <-<{ Γ; T} (tlete e (vbvar 0)).
Proof.
  intros. constructor; auto.
  - auto_exists_L; simpl; intros. basic_typing_vfavr_solver.
  - unfold termRraw. intros Γv. intros. reduction_simpl1.
     rewrite lete_step_spec. split; auto. eexists; split; eauto. reduction_solver1.
Qed.

Lemma lete_0_reduce_to_self': ∀ (Γ : listctx ty) (T : ty) e,
    Γ ⊢t e ⋮t T -> (tlete e (vbvar 0)) <-<{ Γ; T} e.
Proof.
  intros. constructor; auto.
  - auto_exists_L; simpl; intros. basic_typing_vfavr_solver.
  - unfold termRraw. intros Γv. intros. reduction_simpl1.
    rewrite lete_step_spec in H1; mydestr. simpl in H3. reduction_simpl1; auto.
Qed.

Lemma vfix_implies_open_tyable:
  ∀ (Γ : context) e1 (v2: value) (Tx T : ty),
    Γ ⊢t vfix (Tx ⤍ T) (vlam Tx e1) ⋮v Tx ⤍ T →
    Γ ⊢t v2 ⋮v Tx ->
    Γ ⊢t vlam (Tx ⤍ T) ({1 ~t> v2} e1) ⋮v (Tx ⤍ T) ⤍ T.
Proof.
  intros. invclear H. auto_pose_fv f.
  assert ((Γ ++ [(f, TBase Tx0)]) ⊢t (vlam (Tx0 ⤍ T) e1) ^t^ f ⋮t (Tx0 ⤍ T) ⤍ T) by fast_set_solver.
  apply basic_typing_subst_tm_pre with (u:=v2) in H1; eauto.
  simpl in H1. simpl. lc_simpl4. invclear H1; auto.
Qed.

Lemma letapp_fix_reduce_to_open:
  ∀ (Γ : listctx ty) (Tx T2 : ty) e1 (v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vfix (Tx ⤍ T2) (vlam Tx e1)) ⋮v (Tx ⤍ T2) ->
    (tletapp (vfix (Tx ⤍ T2) (vlam Tx e1)) v2 (vbvar 0)) <-<{ Γ; T2}
      (({1 ~t> v2} e1) ^t^ (vfix (Tx ⤍ T2) (vlam Tx e1))).
Proof.
  intros. constructor.
  - auto_exists_L; simpl; intros. basic_typing_vfavr_solver.
  - eapply vlam_implies_open_tyable with (v2:= vfix (Tx ⤍ T2) (vlam Tx e1)); eauto.
    eapply vfix_implies_open_tyable; eauto.
  - unfold termRraw. intros Γv. intros. unfold mk_app in H2. msubst_simpl.
    rewrite letapp_step_spec in H2; mydestr. destruct H5; mydestr; subst; invclear H5. simpl in H6.
    rewrite letapp_step_spec in H6; mydestr. destruct H8; mydestr; subst; invclear H8. simpl in H9.
    eapply lete_0_reduce_to_self_aux'; eauto. msubst_simpl.
    setoid_rewrite tm_open_then_msubst_k; eauto.
    setoid_rewrite tm_open_then_msubst_k; eauto. msubst_simpl. auto.
Qed.

Lemma letapp_fix_reduce_to_open':
  ∀ (Γ : listctx ty) (Tx T2 : ty) e1 (v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vfix (Tx ⤍ T2) (vlam Tx e1)) ⋮v (Tx ⤍ T2) ->
    (({1 ~t> v2} e1) ^t^ (vfix (Tx ⤍ T2) (vlam Tx e1))) <-<{ Γ; T2} (tletapp (vfix (Tx ⤍ T2) (vlam Tx e1)) v2 (vbvar 0)).
Proof.
  intros. constructor.
  - eapply vlam_implies_open_tyable with (v2:= vfix (Tx ⤍ T2) (vlam Tx e1)); eauto.
    apply vfix_implies_open_tyable; auto.
  - auto_exists_L; simpl; intros. basic_typing_vfavr_solver.
  - unfold termRraw. intros Γv. intros. msubst_simpl.
    assert (lc (vfix (Tx ⤍ T2) (vlam Tx e1))) as Hfixlc by basic_typing_solver.
    assert (lc (value_msubst Γv (vfix (Tx ⤍ T2) (vlam Tx e1)))) as Hfixlc'.
    { eapply instantiation_implies_value_msubst_lc; eauto. }
    rewrite letapp_step_spec. repeat split; auto. msubst_simpl; auto.
    reduction_solver1.
    right. do 3 eexists; split; eauto. simpl.
    rewrite letapp_step_spec. repeat split; auto.
    { eapply vfix_implies_open_tyable with (T:=T2) (e1:=e1) (v2:=v2) in H0; eauto.
      assert (lc (vlam (Tx ⤍ T2) ({1 ~t> v2} e1))). basic_typing_solver.
      eapply instantiation_implies_value_msubst_lc in H3; eauto. msubst_simpl.
      setoid_rewrite tm_open_then_msubst_k in H3; eauto. }
    reduction_solver1.
    left. do 2 eexists; split; eauto. simpl.
    eapply lete_0_reduce_to_self_aux in H2; eauto. msubst_simpl.
    setoid_rewrite tm_open_then_msubst_k in H2; eauto.
    setoid_rewrite tm_open_then_msubst_k in H2; eauto. msubst_simpl. auto.
Qed.

Lemma termR_trans_better:
  ∀ (Γ : context) (T : ty) (e1 e2 e3 : tm),
    e1 <-<{ Γ; T} e2 → e2 <-<{ Γ; T} e3 → e1 <-<{ Γ; T} e3.
Proof.
  intros. eapply termR_trans; eauto.
  - invclear H; auto.
  - invclear H; auto.
  - invclear H0; auto.
Qed.

Lemma mk_app_reduce_to_open_fix:
  ∀ (Γ : listctx ty) (Tx T2 : ty) e1 (v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vfix (Tx ⤍ T2) (vlam Tx e1)) ⋮v (Tx ⤍ T2) ->
    (mk_app (vfix (Tx ⤍ T2) (vlam Tx e1)) v2) <-<{ Γ; T2}
      (({1 ~t> v2} e1) ^t^ (vfix (Tx ⤍ T2) (vlam Tx e1))).
Proof.
  intros. apply termR_trans_better with (e2:= tletapp (vfix (Tx ⤍ T2) (vlam Tx e1)) v2 (vbvar 0)).
  - eapply mk_app_v_v_reduce_to_letapp; eauto.
  - eapply letapp_fix_reduce_to_open; eauto.
Qed.

Lemma mk_app_reduce_to_open_fix':
  ∀ (Γ : listctx ty) (Tx T2 : ty) e1 (v2 : value),
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vfix (Tx ⤍ T2) (vlam Tx e1)) ⋮v (Tx ⤍ T2) ->
     (({1 ~t> v2} e1) ^t^ (vfix (Tx ⤍ T2) (vlam Tx e1))) <-<{ Γ; T2} (mk_app (vfix (Tx ⤍ T2) (vlam Tx e1)) v2).
Proof.
  intros. apply termR_trans_better with (e2:= tletapp (vfix (Tx ⤍ T2) (vlam Tx e1)) v2 (vbvar 0)).
  - eapply letapp_fix_reduce_to_open'; eauto.
  - eapply mk_app_v_v_reduce_to_letapp'; eauto.
Qed.

Lemma termR_tletapp_fix: forall Γ e1 (v2: value) e b x1 T,
    Γ ⊢t v2 ⋮v b -> Γ ⊢t vfix (b ⤍ x1) (vlam b e1) ⋮v b ⤍ x1 ->
    (exists (L: aset), ∀ y : atom, y ∉ L → (Γ ++ [(y, x1)]) ⊢t e ^t^ y ⋮t T) ->
  (tlete (({1 ~t> v2} e1) ^t^ (vfix (b ⤍ x1) (vlam b e1))) e) <-<{ Γ; T} (tletapp (vfix (b ⤍ x1) (vlam b e1)) v2 e).
Proof.
  intros. constructor; auto.
  - mydestr. econstructor; eauto.
    eapply vlam_implies_open_tyable; eauto.
    apply vfix_implies_open_tyable; auto.
  - mydestr. auto_pose_fv x'. eapply tletapp_typable with (x:=x'); eauto; fast_set_solver.
  - unfold termRraw. intros Γv; intros. reduction_simpl1.
    rewrite letapp_step_spec. repeat split; auto.
    + assert (lc (value_msubst Γv (vfix (b ⤍ x1) (vlam b e1)))).
      eapply instantiation_implies_value_msubst_lc; eauto. basic_typing_solver.
      msubst_simpl; auto.
    + reduction_solver1.
    + apply multi_step_regular in H3; mydestr. lc_solver.
    + setoid_rewrite tm_open_then_msubst_k in H3; eauto.
      setoid_rewrite tm_open_then_msubst_k in H3; eauto.
      right. do 3 eexists; split; eauto.
      rewrite letapp_step_spec. repeat split; auto.
      { apply vfix_implies_open_tyable with (v2:=v2) in H0; auto.
        assert (lc (value_msubst Γv (vlam (b ⤍ x1) ({1 ~t> v2} e1)))).
        eapply instantiation_implies_value_msubst_lc; eauto. basic_typing_solver.
        simpl. msubst_simpl; auto. simpl. erewrite tm_open_then_msubst_k in H4; eauto. }
      { assert (lc (vfix (b ⤍ x1) (vlam b e1))) by basic_typing_solver.
        eapply instantiation_implies_value_msubst_lc in H4; eauto. msubst_simpl; auto. }
      { mydestr. assert (body e). auto_exists_L. intros a; intros. specialize_with a.
        basic_typing_solver.
        eapply msubst_preserves_body_tm; eauto.
      }
      left. do 2 eexists; split; eauto. msubst_simpl; auto.
Qed.

Lemma termR_tletapp_lam: forall Γ e1 (v2: value) e Tx Ty T,
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vlam Tx e1) ⋮v Tx ⤍ Ty ->
    (exists (L: aset), ∀ y : atom, y ∉ L → (Γ ++ [(y, Ty)]) ⊢t e ^t^ y ⋮t T) ->
    (tlete (e1 ^t^ v2) e) <-<{Γ; T} (tletapp (vlam Tx e1) v2 e).
Proof.
  intros. constructor; auto.
  - mydestr. econstructor; eauto. invclear H0.
    auto_pose_fv x'.
    assert ((Γ ++ [(x', Tx)]) ⊢t e1 ^t^ x' ⋮t Ty). apply H4; fast_set_solver.
    apply basic_typing_subst_tm_pre with (u:=v2) in H2; auto. lc_simpl4.
  - mydestr. auto_pose_fv x'. eapply tletapp_typable with (x:=x'); eauto; fast_set_solver.
  - unfold termRraw. intros Γv; intros. reduction_simpl1.
    rewrite letapp_step_spec. repeat split; auto.
    + assert (lc (value_msubst Γv (vlam Tx e1))).
      eapply instantiation_implies_value_msubst_lc; eauto. basic_typing_solver.
      msubst_simpl; auto.
    + reduction_solver1.
    + apply multi_step_regular in H3; mydestr. lc_solver.
    + left. do 2 eexists; split; eauto.
      setoid_rewrite tm_open_then_msubst_k in H3; eauto.
Qed.

Lemma termR_tletapp_lam_y: forall Γ e1 y (v2: value) e Tx Ty T,
    Γ ⊢t v2 ⋮v Tx -> Γ ⊢t (vlam Tx e1) ⋮v Tx ⤍ Ty -> y # e ->
    (Γ ++ [(y, Ty)]) ⊢t e ^t^ y ⋮t T ->
    (tlete (e1 ^t^ v2) e) <-<{Γ; T} (tletapp (vlam Tx e1) v2 e).
Proof.
  intros. constructor; auto.
  - econstructor; eauto. instantiate (1:=Ty). basic_typing_solver.
    auto_exists_L_intros.
    apply basic_has_type_renaming with (x0:=x) in H2; try listctx_set_solver.
    lc_simpl4. basic_typing_solver.
  - eapply tletapp_typable with (x:=y); eauto; fast_set_solver.
  - unfold termRraw. intros Γv; intros. reduction_simpl1.
    rewrite letapp_step_spec. repeat split; auto.
    + assert (lc (value_msubst Γv (vlam Tx e1))).
      eapply instantiation_implies_value_msubst_lc; eauto. basic_typing_solver.
      msubst_simpl; auto.
    + reduction_solver1.
    + apply multi_step_regular in H4; mydestr. lc_solver.
    + left. do 2 eexists; split; eauto.
      setoid_rewrite tm_open_then_msubst_k in H4; eauto.
Qed.

Lemma mk_app_open: forall e v,
    lc e -> (mk_app e (vbvar 1) ^t^ v) = mk_app e v.
Proof.
  intros. simpl. unfold mk_app. lc_simpl.
Qed.

Lemma termR_elete_better
  : ∀ (γ : listctx ty) (Tx T : ty) (e_x e_x' e e' : tm) (x : atom),
    x ∉ stale e ∪ stale e' ->
    e_x <-<{ γ; Tx} e_x'
    → (e ^t^ x) <-<{ γ ++ [(x, Tx)]; T}(e' ^t^ x)
    → (tlete e_x e) <-<{ γ; T} (tlete e_x' e').
Proof.
  intros.
  eapply termR_elete in H1; eauto.
  rewrite close_open_var_tm in H1; try fast_set_solver.
  rewrite close_open_var_tm in H1; try fast_set_solver.
Qed.

Lemma termR_elete_lhs
  : ∀ (γ : listctx ty) (Tx T : ty) (e_x e_x' e : tm) (x : atom),
    x ∉ stale e ->
    e_x <-<{ γ; Tx} e_x' -> (γ ++ [(x, Tx)]) ⊢t (e ^t^ x) ⋮t T
    → (tlete e_x e) <-<{ γ; T} (tlete e_x' e).
Proof.
  intros. eapply termR_elete_better; eauto. fast_set_solver.
Qed.

Lemma termRraw_weakening: forall Γ e e',
    closed_tm e -> closed_tm e' -> termRraw [] e e' -> termRraw Γ e e'.
Proof.
  unfold termRraw. intros. rewrite tm_msubst_closed; auto.
  rewrite tm_msubst_closed in H3; auto.
  assert (instantiation [] []) as Hz; auto.
  eapply H1 in Hz; eauto.
Qed.

Lemma termR_weakening: forall Γ T e e',
    ok Γ -> e <-<{ []; T} e' -> e <-<{ Γ; T} e'.
Proof.
  intros. invclear H0. constructor; basic_typing_solver.
  eapply termRraw_weakening; auto; basic_typing_solver.
Qed.

Lemma termR_value_tm: forall T e (v: value),
    [] ⊢t e ⋮t T -> e ↪* v -> v <-<{ []; T} e.
Proof.
  intros. constructor; auto.
  - eapply multi_preservation; eauto.
  - unfold termRraw. intros Γv; intros. invclear H1.
    simpl in H2. simpl. eapply multistep_trans; eauto.
Qed.


Definition eval_op_under_bound_tm (op: biop) (a: nat) (b: nat): tm :=
  match op with
  | op_plus => a + b
  | op_eq => (Nat.eqb a b)
  | op_lt => (Nat.ltb a b)
  | op_rannat => nat-gen
  end.

Definition eval_op_under_bound_tm_all (op: biop) (a: value) (b: value): tm :=
  tletbiop op_eq a b (vbvar 0).

Lemma eval_op_under_bound_tm_reduction_sepc: forall (op: biop) (a: nat) (b: nat) (c: constant),
    eval_op op a b c ->
    eval_op_under_bound_tm op a b ↪* c.
Proof.
  destruct op; simpl; intros; invclear H; auto.
Qed.

Global Hint Resolve eval_op_under_bound_tm_reduction_sepc: core.

Lemma eval_op_under_bound_tm_reduction_sepc': forall (op: biop) (a: nat) (b: nat) (c: constant),
    eval_op_under_bound_tm op a b ↪* c ->
    eval_op op a b c.
Proof.
  destruct op; simpl; intros.
  - rewrite value_reduce_to_value_implies_same in H; mydestr; subst.
    invclear H. constructor.
  - rewrite value_reduce_to_value_implies_same in H; mydestr; subst.
    invclear H. constructor.
  - rewrite value_reduce_to_value_implies_same in H; mydestr; subst.
    invclear H. constructor.
  - assert ([] ⊢t nat-gen ⋮t TNat); auto.
    assert ([] ⊢t c ⋮t TNat). eapply multi_preservation; eauto.
    invclear H1. invclear H4. destruct c; invclear H3. constructor.
Qed.

Global Hint Resolve eval_op_under_bound_tm_reduction_sepc': core.

Lemma eval_op_under_bound_tm_tyable: forall (op: biop) (a: nat) (b: nat),
    [] ⊢t eval_op_under_bound_tm op a b ⋮t ret_ty_of_op op.
Proof.
  destruct op; simpl; intros; eauto.
  - do 2 constructor; auto.
  - do 2 constructor; auto.
  - do 2 constructor; auto.
Qed.

Global Hint Resolve eval_op_under_bound_tm_tyable: core.

Lemma termR_tmatchb_true: forall Γ T e1 e2,
  Γ ⊢t e1 ⋮t T -> Γ ⊢t e2 ⋮t T ->
  e1 <-<{ Γ; T} (tmatchb true e1 e2).
Proof.
  intros. constructor; auto.
  - repeat constructor; auto. basic_typing_solver.
  - unfold termRraw. intros Γv; intros. assert (closed_value true) by auto.
    reduction_simpl1. rewrite value_msubst_closed; auto.
    eapply multistep_step; eauto. constructor; auto; reduction_solver1.
Qed.

Lemma termR_tmatchb_false: forall Γ T e1 e2,
  Γ ⊢t e1 ⋮t T -> Γ ⊢t e2 ⋮t T ->
  e2 <-<{ Γ; T} (tmatchb false e1 e2).
Proof.
  intros. constructor; auto.
  - repeat constructor; auto. basic_typing_solver.
  - unfold termRraw. intros Γv; intros. assert (closed_value false) by auto.
    reduction_simpl1. rewrite value_msubst_closed; auto.
    eapply multistep_step; eauto. constructor; auto; reduction_solver1.
Qed.
