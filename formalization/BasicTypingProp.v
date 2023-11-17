From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import BasicTyping.
From CT Require Import OperationalSemantics.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import BasicTyping.
Import Trace.
Import OperationalSemantics.

Lemma basic_typing_weaken_tm: forall Γ Γ' (v: tm) T,
    Γ ⊆ Γ' -> Γ ⊢t v ⋮t T -> Γ' ⊢t v ⋮t T
with basic_typing_weaken_value: forall Γ Γ' (v: value) T,
    Γ ⊆ Γ' -> Γ ⊢t v ⋮v T -> Γ' ⊢t v ⋮v T.
Proof.
  all : intros * Hs; destruct 1; econstructor; eauto using lookup_weaken.
  all: instantiate_atom_listctx;
    auto_eapply;
    try lazymatch goal with
      | |- _ ⊆ _ => apply insert_mono; eauto
      | _ => eauto
      end.
Qed.

Lemma basic_typing_weaken_insert_tm: forall Γ (v: tm) T x U,
    x # Γ -> Γ ⊢t v ⋮t T -> <[x := U]>Γ ⊢t v ⋮t T.
Proof.
  intros. eapply basic_typing_weaken_tm. 2: eauto.
  apply insert_subseteq. apply not_elem_of_dom. my_set_solver.
Qed.

Lemma basic_typing_weaken_insert_value: forall Γ (v: value) T x U,
    x # Γ -> Γ ⊢t v ⋮v T -> <[x := U]> Γ ⊢t v ⋮v T.
Proof.
  intros. eapply basic_typing_weaken_value. 2: eauto.
  apply insert_subseteq. apply not_elem_of_dom. my_set_solver.
Qed.

Lemma basic_typing_subst_tm: forall Γ z u U (v: tm) T, Γ ⊢t u ⋮v U -> <[z := U]> Γ ⊢t v ⋮t T -> Γ ⊢t {z := u}t v ⋮t T.
Proof.
  intros * Hu Ht; remember (<[z:=U]> Γ) as Γ'; generalize dependent Γ.
  revert Γ' v T Ht.
  apply (tm_has_type_mutual_rec
           (fun c v T _ => ∀ Γ, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }v v ⋮v T)
           (fun c v T _ => ∀ Γ, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }t v ⋮t T));
  (* [context] should be defined as a notation which helps resolving typeclass
  instances for, e.g., rewriting. *)
    unfold context;
    intros; subst; simpl in *; eauto; try econstructor; eauto.
  case_decide; subst.
  by simplify_map_eq.
  econstructor. by simplify_map_eq.

  all:
  instantiate_atom_listctx;
  rewrite <- subst_open_var_tm by
    (eauto using basic_typing_regular_value; my_set_solver);
  auto_eapply; [
      eapply basic_typing_weaken_insert_value; eauto; my_set_solver
    | apply insert_commute; my_set_solver ].
Qed.

Lemma basic_typing_subst_value: forall Γ z u U (v: value) T, Γ ⊢t u ⋮v U -> <[z := U]> Γ ⊢t v ⋮v T -> Γ ⊢t {z := u}v v ⋮v T.
Proof.
  intros * Hu Ht; remember (<[z:=U]> Γ) as Γ'; generalize dependent Γ.
  revert Γ' v T Ht.
  apply (value_has_type_mutual_rec
           (fun c v T _ => ∀ Γ, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }v v ⋮v T)
           (fun c v T _ => ∀ Γ, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }t v ⋮t T));
    unfold context;
    intros; subst; simpl in *; eauto; try econstructor; eauto.
  case_decide; subst.
  by simplify_map_eq.
  econstructor. by simplify_map_eq.

  all:
  instantiate_atom_listctx;
  rewrite <- subst_open_var_tm by
    (eauto using basic_typing_regular_value; my_set_solver);
  auto_eapply; [
      eapply basic_typing_weaken_insert_value; eauto; my_set_solver
    | apply insert_commute; my_set_solver ].
Qed.

Lemma basic_typing_tm_unique: forall Γ e T1 T2,
    Γ ⊢t e ⋮t T1 ->
    Γ ⊢t e ⋮t T2 ->
    T1 = T2.
Proof.
  intros * H. revert T2. revert_all.
  apply (tm_has_type_mutual_rec
           (fun Γ v T1 _ => ∀ T2, Γ ⊢t v ⋮v T2 → T1 = T2)
           (fun Γ e T1 _ => ∀ T2, Γ ⊢t e ⋮t T2 → T1 = T2));
    intros;
    try match goal with
      | H : _ ⊢t _ ⋮t _ |- _ => sinvert H
      | H : _ ⊢t _ ⋮v _ |- _ => sinvert H
      end; eauto;
    try solve [ auto_pose_fv x; repeat specialize_with x; hauto ].
  by simplify_map_eq.
Qed.

Lemma basic_typing_value_unique: forall Γ v T1 T2,
    Γ ⊢t v ⋮v T1 ->
    Γ ⊢t v ⋮v T2 ->
    T1 = T2.
Proof.
  intros * H. revert T2. revert_all.
  apply (value_has_type_mutual_rec
           (fun Γ v T1 _ => ∀ T2, Γ ⊢t v ⋮v T2 → T1 = T2)
           (fun Γ e T1 _ => ∀ T2, Γ ⊢t e ⋮t T2 → T1 = T2));
    intros;
    try match goal with
      | H : _ ⊢t _ ⋮t _ |- _ => sinvert H
      | H : _ ⊢t _ ⋮v _ |- _ => sinvert H
      end; eauto;
    try solve [ auto_pose_fv x; repeat specialize_with x; hauto ].
  by simplify_map_eq.
Qed.

(* This statement can be generalized to taking a union of the context and a
disjoint new context. *)
Lemma basic_typing_strengthen_tm: forall Γ x Tx (v: tm) T,
    (<[x:=Tx]>Γ) ⊢t v ⋮t T -> x # v -> Γ ⊢t v ⋮t T
with basic_typing_strengthen_value: forall Γ x Tx (v: value) T,
    (<[x:=Tx]>Γ) ⊢t v ⋮v T -> x # v -> Γ ⊢t v ⋮v T.
Proof.
  all : intros * H Hfresh; remember (<[x:=Tx]>Γ);
    generalize dependent Γ;
    destruct H; intros; unfold context in *; subst;
    econstructor; eauto;
    try solve [
        try instantiate_atom_listctx;
        try rewrite insert_commute in * by my_set_solver;
        auto_eapply; eauto;
        match goal with
        | |- context [{_ ~t> _} _] =>
            eapply not_elem_of_weaken; [ | apply open_fv_tm ]; my_set_solver
        | _ => my_set_solver
        end ].
  by rewrite lookup_insert_ne in * by my_set_solver.
Qed.

Lemma mk_app_e_v_has_type Γ e v T1 T2 :
  Γ ⊢t e ⋮t T1 ⤍ T2 ->
  Γ ⊢t v ⋮v T1 ->
  Γ ⊢t mk_app_e_v e v ⋮t T2.
Proof.
  intros.
  econstructor; eauto.
  instantiate_atom_listctx.
  simpl. econstructor. econstructor. simplify_map_eq. reflexivity.
  rewrite open_rec_lc_value by eauto using basic_typing_regular_value.
  apply basic_typing_weaken_insert_value; eauto. my_set_solver.
  simpl. instantiate_atom_listctx. econstructor. econstructor. simplify_map_eq.
  reflexivity.
Qed.

Lemma mk_app_e_v_has_type_inv Γ e v T2 :
  Γ ⊢t mk_app_e_v e v ⋮t T2 ->
  lc v ->
  exists T1, Γ ⊢t e ⋮t T1 ⤍ T2 /\ Γ ⊢t v ⋮v T1.
Proof.
  intros.
  sinvert H.
  simpl in H6.
  auto_pose_fv x. repeat specialize_with x.
  rewrite open_rec_lc_value in H6 by auto.
  sinvert H6. simpl in H10.
  auto_pose_fv y. repeat specialize_with y.
  sinvert H7. setoid_rewrite lookup_insert in H5. simplify_eq.
  sinvert H10. sinvert H5. setoid_rewrite lookup_insert in H6. simplify_eq.
  repeat esplit; eauto.
  eapply basic_typing_strengthen_value; eauto. my_set_solver.
Qed.

Lemma tr_reduction_sound α op c1 c :
  α⊧{op~c1}⇓{c} ->
  ty_of_const c = ret_ty_of_op op.
Proof.
  induction 1; eauto.
Qed.

(** perservation *)
Lemma preservation: forall α β Γ T (e e': tm),α ⊧ e ↪{ β } e' -> Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T.
Proof.
  intros * Hstep HT. move HT at top. revert_all.
  induction 1; intros; sinvert Hstep; eauto.
  - auto_pose_fv x. repeat specialize_with x.
    rewrite <- subst_intro_tm with (x:=x) by (eauto; my_set_solver).
    sinvert HT. eauto using basic_typing_subst_tm.
  - auto_pose_fv x. repeat specialize_with x.
    rewrite <- subst_intro_tm with (x:=x) by (eauto; my_set_solver).
    sinvert H0. erewrite <- tr_reduction_sound in H1; eauto.
    eauto using basic_typing_subst_tm.
  - sinvert H.
    econstructor; eauto.
    auto_pose_fv x. repeat specialize_with x.
    rewrite <- subst_intro_tm with (x:=x) by (eauto; my_set_solver).
    eauto using basic_typing_subst_tm.
  - sinvert H.
    econstructor; eauto.
    auto_pose_fv x. repeat specialize_with x.
    rewrite <- subst_intro_value with (x:=x) by (eauto; my_set_solver).
    eauto using basic_typing_subst_value.
Qed.

(** multi preservation *)
Lemma multi_preservation: forall α β Γ T (e e': tm),α ⊧ e ↪*{ β } e' -> Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T.
Proof.
  induction 1; eauto using preservation.
Qed.
