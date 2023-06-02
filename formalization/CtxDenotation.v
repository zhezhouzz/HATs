From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.
From CT Require Import RefinementTypeDenotation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import OperationalSemanticsProp.
Import BasicTyping.
Import SyntaxSugar.
Import RefinementType.
Import RefinementTypeTac.
Import RefinementTypeDenotation.

(** Type denotation under type context *)
Inductive ctxrR: state -> listctx rty -> rty -> tm -> Prop :=
| ctxrR_nil: forall st τ e, { st }⟦ τ ⟧ e -> ctxrR st [] τ e
| ctxrR_cons_over: forall st (x: atom) b n d ϕ Γ τ (e: tm),
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ ->
    ok_dctx (dom _ st) ((x, {v: b | n | d | ϕ}) :: Γ) ->
    ((x, TBase b) :: (⌊Γ⌋*)) ⊢t e ⋮t ⌊τ⌋ ->
     (forall (c_x: constant), {st}⟦ {v: b | n | d | ϕ} ⟧ c_x ->
                         ctxrR (<[ x := c_x ]> st) Γ τ ({x := c_x}t e)) ->
     ctxrR st ((x, {v: b | n | d | ϕ}) :: Γ) τ e
| ctxrR_cons_under_base: forall st (x: atom) b n d ϕ τ Γ e,
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ ->
    ok_dctx (dom _ st) ((x, [v: b | n | d | ϕ]) :: Γ) ->
    ((x, TBase b) :: (⌊Γ⌋*)) ⊢t e ⋮t ⌊τ⌋ ->
     (exists e_x_hat, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x_hat /\
                   (forall e_x, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x ->
                           (∀ (v_x: value), e_x_hat ↪* v_x -> e_x ↪* v_x ->
                                            ctxrR ({ x ↦ v_x } st) Γ τ (tlete e_x ({ 0 <t~ x} e))))) ->
     ctxrR st ((x, [v: b | n | d | ϕ]) :: Γ) τ e
| ctxrR_cons_under_arr: forall st (x: atom) τ_x τ Γ e,
    is_arr τ_x ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ ->
    ok_dctx (dom _ st) ((x, τ_x) :: Γ) ->
    ((x, ⌊τ_x⌋ ) :: (⌊Γ⌋*)) ⊢t e ⋮t ⌊τ⌋ ->
     (exists e_x_hat, {st}⟦ τ_x ⟧ e_x_hat /\
                   (forall (e_x: value), {st}⟦ τ_x ⟧ e_x ->
                           (∀ (v_x: value), e_x_hat ↪* v_x -> e_x ↪* v_x ->
                                            ctxrR ({ x ↦ v_x } st) Γ τ (tlete e_x ({ 0 <t~ x} e))))) ->
     ctxrR st ((x, τ_x) :: Γ) τ e.

Notation " '{' st '}⟦' τ '⟧{' Γ '}' " := (ctxrR st Γ τ) (at level 20, format "{ st }⟦ τ ⟧{ Γ }", st constr, τ constr, Γ constr).

Lemma ctxrR_regular0:
  forall Γ τ st e, { st }⟦ τ ⟧{ Γ } e ->
              closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ /\ ok_dctx (dom _ st) Γ.
Proof.
  induction Γ; simpl; intros; invclear H; simpl; auto; dec_solver2.
  - apply rR_regular2 in H0; mydestr. constructor; simpl; auto.
    + closed_rty_solver.
    + constructor.
Qed.

Lemma ctxrR_regular1:
  forall Γ τ st e, { st }⟦ τ ⟧{ Γ } e ->
              (ok_dctx (dom _ st) Γ) /\
                ctx_closed_rty (dom _ st) Γ /\
                closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ.
Proof.
  intros. apply ctxrR_regular0 in H. mydestr.
  do 2 (split; auto). apply ok_dctx_regular2 in H0; mydestr; auto.
Qed.

Lemma ctxrR_regular2:
  forall Γ τ st e, { st }⟦ τ ⟧{ Γ } e -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  induction Γ; simpl; intros; invclear H; simpl; auto.
  - apply rR_regular2 in H0; mydestr; auto.
Qed.

Lemma ctxrR_regular:
  forall Γ τ st e, { st }⟦ τ ⟧{ Γ } e ->
              ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋ /\
                (ok_dctx (dom _ st) Γ) /\
                ctx_closed_rty (dom _ st) Γ /\
                closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ.
Proof.
  intros. split.
  - eapply ctxrR_regular2; eauto.
  - eapply ctxrR_regular1; eauto.
Qed.


(** Subtype denotation under type context *)
Inductive ctxrR2: state -> listctx rty -> rty -> rty -> Prop :=
| ctxrR2_nil: forall st τ1 τ2,
    closed_rty 0 (dom _ st) τ1 -> closed_rty 0 (dom _ st) τ2 ->
    ⌊ τ1 ⌋ = ⌊ τ2 ⌋ ->
    (forall e, { st }⟦ τ1 ⟧ e -> { st }⟦ τ2 ⟧ e) ->
    ctxrR2 st [] τ1 τ2
| ctxrR2_cons_over: forall st (x: atom) b n d ϕ Γ τ1 τ2,
    ok_dctx (dom _ st) ((x, {v: b | n | d | ϕ}) :: Γ) ->
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ dom _ st) τ1 ->
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ dom _ st) τ2 ->
    ⌊ τ1 ⌋ = ⌊ τ2 ⌋ ->
    (forall (c_x: constant), {st}⟦ {v: b | n | d | ϕ} ⟧ c_x -> ctxrR2 (<[ x := c_x ]> st) Γ τ1 τ2) ->
    ctxrR2 st ((x, {v: b | n | d | ϕ}) :: Γ) τ1 τ2
| ctxrR2_cons_under_base: forall st (x: atom) b n d ϕ τ1 τ2 Γ,
    ok_dctx (dom _ st) ((x, [v: b | n | d | ϕ]) :: Γ) ->
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ dom _ st) τ1 ->
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ dom _ st) τ2 ->
    ⌊ τ1 ⌋ = ⌊ τ2 ⌋ ->
    (exists e_x_hat, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x_hat /\
                  (forall e_x, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x ->
                          (∀ (v_x: value), e_x_hat ↪* v_x -> e_x ↪* v_x -> ctxrR2 ({ x ↦ v_x } st) Γ τ1 τ2))) ->
    ctxrR2 st ((x, [v: b | n | d | ϕ]) :: Γ) τ1 τ2
| ctxrR2_cons_under_arr: forall st (x: atom) τ_x τ1 τ2 Γ,
    is_arr τ_x ->
    ok_dctx (dom _ st) ((x, τ_x) :: Γ) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) τ1 ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) τ2 ->
    ⌊ τ1 ⌋ = ⌊ τ2 ⌋ ->
    (exists e_x_hat, {st}⟦ τ_x ⟧ e_x_hat /\
                  (forall e_x, {st}⟦ τ_x ⟧ e_x ->
                          (∀ (v_x: value), e_x_hat ↪* v_x -> e_x ↪* v_x -> ctxrR2 ({ x ↦ v_x } st) Γ τ1 τ2))) ->
    ctxrR2 st ((x, τ_x) :: Γ) τ1 τ2.

Notation " '{' st '}⟦' τ1 '⟧⊆⟦' τ2 '⟧{' Γ '}' " := (ctxrR2 st Γ τ1 τ2) (at level 20, format "{ st }⟦ τ1 ⟧⊆⟦ τ2 ⟧{ Γ }", st constr, τ1 constr, τ2 constr, Γ constr).
