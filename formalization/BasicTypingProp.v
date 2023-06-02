From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import BasicTyping.
From CT Require Import OperationalSemantics.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import BasicTyping.
Import Equation.
Import OperationalSemantics.

Lemma basic_typing_weaken_value: forall Γ Γ' (v: value) T,
    Γ ⊆ Γ' -> Γ ⊢t v ⋮v T -> Γ' ⊢t v ⋮v T.
Admitted.

Lemma basic_typing_weaken_tm: forall Γ Γ' (v: tm) T,
    Γ ⊆ Γ' -> Γ ⊢t v ⋮t T -> Γ' ⊢t v ⋮t T.
Admitted.

Lemma basic_typing_subst_value: forall Γ z u U (v: value) T, Γ ⊢t u ⋮v U -> <[z := U]> Γ ⊢t v ⋮v T -> Γ ⊢t {z := u}v v ⋮v T.
Admitted.

Lemma basic_typing_subst_tm: forall Γ z u U (v: tm) T, Γ ⊢t u ⋮v U -> <[z := U]> Γ ⊢t v ⋮t T -> Γ ⊢t {z := u}t v ⋮t T.
Admitted.

Lemma eval_op_type_safe: forall α op (v1 v: value) (T1 T: base_ty),
    α +;+ (op :{ v1 }) ⇓ v ->
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

Lemma tyable_includes_fv_tm: forall (Γ: context) e T, Γ ⊢t e ⋮t T -> (fv_tm e) ⊆ (dom _ Γ).
Admitted.

Lemma tyable_includes_fv_value: forall Γ e T, Γ ⊢t e ⋮v T -> (fv_value e) ⊆ (dom _ Γ).
Admitted.
