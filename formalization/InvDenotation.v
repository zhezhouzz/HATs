From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin_map_dom.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.
From CT Require Import RefinementTypeDenotation.
From CT Require Import RefinementTypeDenotationTac.
From CT Require Import RefinementTypeDenotationProp.
From CT Require Import WFCtxDenotationProp.
From CT Require Import TermOrdering.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.

Import Atom.
Import CoreLang.
Import CoreLangProp.
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
Import RefinementTypeDenotationTac.
Import RefinementTypeDenotationProp.
Import WFCtxDenotation.
Import WFCtxDenotationProp.
Import NamelessTactics.
Import TermOrdering.

Global Hint Resolve mk_eq_constant_is_not_overbasety: core.
Global Hint Resolve mk_eq_var_is_not_overbasety: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Constructors ok_dctx: core.
Global Hint Resolve rR_implies_no_free: core.
Global Hint Resolve ctxrR_tlete_drop_halt_lhs: core.
Global Hint Resolve rR_implies_reduction_no_free: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Resolve under_not_overbasety: core.

Inductive inv_ctxrR: state -> listctx rty -> rty -> tm -> Prop :=
| inv_ctxrR_nil: forall st τ e, { st }⟦ τ ⟧ e -> inv_ctxrR st [] τ e
| inv_ctxrR_cons_over: forall st (x: atom) B n d ϕ Γ τ (e: tm),
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ ->
    ok_dctx (dom _ st) ((x, {v: B | n | d | ϕ}) :: Γ) ->
    ((x, TBase B) :: (⌊Γ⌋*)) ⊢t e ⋮t ⌊τ⌋ ->
     (forall (c_x: constant), {st}⟦ {v: B | n | d | ϕ} ⟧ c_x ->
                         inv_ctxrR (<[ x := c_x ]> st) Γ τ ({x := c_x}t e)) ->
     inv_ctxrR st ((x, {v: B | n | d | ϕ}) :: Γ) τ e
| inv_ctxrR_cons_under_base: forall st (x: atom) b n d ϕ τ Γ e,
    closed_rty 0 ({[x]} ∪ ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ ->
    ok_dctx (dom _ st) ((x, [v: b | n | d | ϕ]) :: Γ) ->
    ((x, TBase b ) :: (⌊Γ⌋*)) ⊢t e ⋮t ⌊τ⌋ ->
     (exists e_x_hat, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x_hat /\
                   (∀ (v_x: value), e_x_hat ↪* v_x ->
                                       inv_ctxrR ({ x ↦ v_x } st) Γ τ ({x := v_x}t e))) ->
     inv_ctxrR st ((x, [v: b | n | d | ϕ]) :: Γ) τ e
| inv_ctxrR_cons_under_arr: forall st (x: atom) τ_x τ Γ e,
    is_arr τ_x ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ ->
    ok_dctx (dom _ st) ((x, τ_x) :: Γ) ->
    ((x, ⌊τ_x⌋ ) :: (⌊Γ⌋*)) ⊢t e ⋮t ⌊τ⌋ ->
     (forall (v_x: value), {st}⟦ τ_x ⟧ v_x -> inv_ctxrR st Γ τ ({x := v_x}t e)) ->
     inv_ctxrR st ((x, τ_x) :: Γ) τ e.

Notation " '⅋{' st '}⟦' τ '⟧{' Γ '}' " := (inv_ctxrR st Γ τ) (at level 20, format "⅋{ st }⟦ τ ⟧{ Γ }", st constr, τ constr, Γ constr).
