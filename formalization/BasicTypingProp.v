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
  intros * Hu Ht; remember (<[z:=U]> Γ); revert dependent Γ.
  revert c v T Ht.
  apply (tm_has_type_mutual_rec
           (fun c v T _ => ∀ Γ : context, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }v v ⋮v T)
           (fun c v T _ => ∀ Γ : context, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }t v ⋮t T)); intros; subst; simpl in *; eauto; try econstructor; eauto.
  case_decide; subst.
  (* For some reason normal rewrite does not work. *)
  setoid_rewrite lookup_insert in e. simplify_eq. eauto.
  econstructor. setoid_rewrite lookup_insert_ne in e; eauto.

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
  intros * Hu Ht; remember (<[z:=U]> Γ); revert dependent Γ.
  revert c v T Ht.
  apply (value_has_type_mutual_rec
           (fun c v T _ => ∀ Γ : context, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }v v ⋮v T)
           (fun c v T _ => ∀ Γ : context, Γ ⊢t u ⋮v U → c = <[z:=U]> Γ → Γ ⊢t {z := u }t v ⋮t T)); intros; subst; simpl in *; eauto; try econstructor; eauto.
  case_decide; subst.
  (* For some reason normal rewrite does not work. *)
  setoid_rewrite lookup_insert in e. simplify_eq. eauto.
  econstructor. setoid_rewrite lookup_insert_ne in e; eauto.

  all:
  instantiate_atom_listctx;
  rewrite <- subst_open_var_tm by
    (eauto using basic_typing_regular_value; my_set_solver);
  auto_eapply; [
      eapply basic_typing_weaken_insert_value; eauto; my_set_solver
    | apply insert_commute; my_set_solver ].
Qed.

Lemma eval_op_type_safe: forall α op (v1 v: constant) (T1 T: base_ty),
    α ⊧{ op ~ v1 }⇓{ v } ->
    ty_of_op op = T1 ⤍ T ->
    ∅ ⊢t v1 ⋮v T1 /\ ∅ ⊢t v ⋮v T.
Admitted.

Lemma ty_tlete_dummy: forall Γ Tx T (e_x e: tm), Γ ⊢t e_x ⋮t Tx -> Γ ⊢t e ⋮t T -> Γ ⊢t (tlete e_x e) ⋮t T.
Admitted.

(** perservation *)
Lemma preservation: forall α β Γ T (e e': tm),α ⊧ e ↪{ β } e' -> Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T.
Admitted.

(** multi preservation *)
Lemma multi_preservation: forall α β Γ T (e e': tm),α ⊧ e ↪*{ β } e' -> Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T.
Admitted.

Lemma closed_has_type_under_empty_value: forall Γ (v: value) T, Γ ⊢t v ⋮v T -> closed_value v -> ∅ ⊢t v ⋮v T.
Admitted.

Lemma closed_has_type_under_empty_tm: forall Γ (v: tm) T, Γ ⊢t v ⋮t T -> closed_tm v -> ∅ ⊢t v ⋮t T.
Admitted.

Lemma vlam_tyable_dummy: forall Γ e Tx T,
  Γ ⊢t e ⋮t T -> Γ ⊢t vlam Tx e ⋮v Tx ⤍ T.
Admitted.

Lemma vlam_implies_open_tyable: forall Γ e1 v2 Tx T,
  Γ ⊢t v2 ⋮v Tx -> Γ ⊢t vlam Tx e1 ⋮v Tx ⤍ T -> Γ ⊢t e1 ^t^ v2 ⋮t T.
Admitted.
