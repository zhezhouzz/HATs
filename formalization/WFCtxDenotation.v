From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.
From CT Require Import RefinementTypeDenotation.
From CT Require Import RefinementTypeDenotationTac.

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
Import RefinementTypeDenotationTac.

(* two denotation of the well-found type context *)
Inductive wf_ctxrR_not_terr: state -> listctx rty -> Prop :=
| wf_ctxrR_nil_not_terr: forall st, wf_ctxrR_not_terr st []
| ctxrR_cons_over_not_terr: forall st (x: atom) B n d ϕ Γ,
    ok_dctx (dom _ st) ((x, {v: B | n | d | ϕ}) :: Γ) ->
    (forall (c_x: constant), {st}⟦ {v: B | n | d | ϕ} ⟧ c_x ->
                        wf_ctxrR_not_terr (<[ x := c_x ]> st) Γ) ->
    wf_ctxrR_not_terr st ((x, {v: B | n | d | ϕ}) :: Γ)
| ctxrR_cons_under_base_not_terr: forall st (x: atom) b n d ϕ Γ,
    ok_dctx (dom _ st) ((x, [v: b | n | d | ϕ]) :: Γ) ->
    ¬ ({st}⟦ [v: b | n | d | ϕ] ⟧ terr) ->
    (exists e_x_hat, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x_hat /\
                  (forall e_x, {st}⟦ [v: b | n | d | ϕ] ⟧ e_x ->
                          (∀ (v_x: value), e_x_hat ↪* v_x -> e_x ↪* v_x ->
                                           wf_ctxrR_not_terr ({ x ↦ v_x } st) Γ ))) ->
    wf_ctxrR_not_terr st ((x, [v: b | n | d | ϕ]) :: Γ)
| ctxrR_cons_under_arr_not_terr: forall st (x: atom) τ_x Γ,
    is_arr τ_x ->
    ok_dctx (dom _ st) ((x, τ_x) :: Γ) ->
    (exists e_x_hat, {st}⟦ τ_x ⟧ e_x_hat /\
                  (forall e_x, {st}⟦ τ_x ⟧ e_x ->
                          (∀ (v_x: value), e_x_hat ↪* v_x -> e_x ↪* v_x ->
                                           wf_ctxrR_not_terr ({ x ↦ v_x } st) Γ ))) ->
    wf_ctxrR_not_terr st ((x, τ_x) :: Γ).

Inductive wf_ctxrR: state -> listctx rty -> Prop :=
| wf_ctxrR_nil: forall st, wf_ctxrR st []
| wf_ctxrR_cons_over: forall st (x: atom) B n d ϕ Γ,
    ok_dctx (dom _ st) ((x, {v: B | n | d | ϕ}) :: Γ) ->
    (forall (c_x: constant), {st}⟦ {v: B | n | d | ϕ} ⟧ c_x ->
                        wf_ctxrR (<[ x := c_x ]> st) Γ) ->
    wf_ctxrR st ((x, {v: B | n | d | ϕ}) :: Γ)
| wf_ctxrR_cons_under_base: forall st (x: atom) B n d ϕ Γ,
    ok_dctx (dom _ st) ((x, [v: B | n | d | ϕ] ) :: Γ) ->
    (forall e_wf, {st}⟦ [v: B | n | d | ϕ] ⟧ e_wf -> (exists (v_wf: value), e_wf ↪* v_wf)) ->
    (exists e_x_hat, {st}⟦ [v: B | n | d | ϕ] ⟧ e_x_hat /\
                  (forall e_x, {st}⟦ [v: B | n | d | ϕ] ⟧ e_x ->
                          (∀ (v_x: value), e_x_hat ↪* v_x ->
                                           wf_ctxrR ({ x ↦ v_x } st) Γ ))) ->
    wf_ctxrR st ((x, [v: B | n | d | ϕ]) :: Γ)
| wf_ctxrR_cons_under_arr: forall st (x: atom) τ_x Γ,
    is_arr τ_x ->
    ok_dctx (dom _ st) ((x, τ_x) :: Γ) ->
    (forall e_wf, {st}⟦ τ_x ⟧ e_wf -> (exists (v_wf: value), e_wf ↪* v_wf)) ->
    wf_ctxrR st Γ ->
    wf_ctxrR st ((x, τ_x) :: Γ).
