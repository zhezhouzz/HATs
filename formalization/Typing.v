From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Denotation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import Equation.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Denotation.

(** Well-formedness *)
Inductive wf_pty: listctx pty -> pty -> Prop :=
| wf_pty_base: forall Γ b ϕ,
    valid_pty {v: b | ϕ } -> closed_pty 0 (ctxdom ⦑ Γ ⦒) {v: b | ϕ } ->  wf_pty Γ {v: b | ϕ }
| wf_pty_arr: forall Γ ρ T A B (L: aset),
    valid_am A ->
    amlist_typed B T ->
    (forall x, x ∉ L ->
          (forall Bi ρi, In (Bi, ρi) B ->
              valid_am Bi /\ wf_pty (Γ ++ [(x, ρ)]) ρi
          )
    ) ->
    wf_pty Γ (-: ρ ⤑[: T | A ⇒ B ]).

Inductive wf_hty: listctx pty -> hty -> Prop :=
| wf_hty_: forall Γ T A B,
    valid_am A ->
    amlist_typed B T ->
    (forall Bi ρi, In (Bi, ρi) B ->
              valid_am Bi /\ wf_pty Γ ρi
    ) ->
    wf_hty Γ [: T | A ⇒ B ].

Notation " Γ '⊢WF' τ " := (wf_hty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFp' τ " := (wf_pty Γ τ) (at level 20, τ constr, Γ constr).

Definition subtyping (Γ: listctx pty) (τ1 τ2: hty) : Prop := forall st, ctxRst Γ st -> forall e, { st }⟦ τ1 ⟧ e -> { st }⟦ τ2 ⟧ e.

Notation " Γ '⊢' τ1 '⪡' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ"  (at level 20).

(** Typing *)
Inductive term_type_check : listctx pty -> tm -> hty -> Prop :=
| TValue: forall Γ v ρ,
    Γ ⊢ v ⋮v ρ ->
    Γ ⊢ v ⋮t (pty_to_rty ρ)
| TSub: forall Γ e (τ1 τ2: hty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 -> Γ ⊢ τ1 ⪡ τ2 -> (Γ ⊢ e ⋮t τ2)
| TLetE: forall Γ e_x e Tx Ax Bx T A B (L: aset),
    Γ ⊢WF [: T | A ⇒ B ] ->
    Γ ⊢ e_x ⋮t [: Tx | Ax ⇒ Bx ] ->
    (forall Bxi ρxi, In (Bxi, ρxi) Bx ->
                exists Bi ρi, In (aconcat Bxi Bi, ρi) B /\
                           (forall x, x ∉ L ->
                                 (Γ ++ [(x, ρxi)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A Bxi ⇒ [(Bi, ρi)]])
    ) ->
    Γ ⊢ (tlete e_x e) ⋮t [: T | A ⇒ B ]
| TApp: forall Γ (v1 v2: value) e ρ Tx Ax Bx T A B (L: aset),
    Γ ⊢WF [: T | A ⇒ B ] ->
    Γ ⊢ v2 ⋮v ρ ->
    Γ ⊢ v1 ⋮v (-: ρ ⤑[: Tx | Ax ⇒ Bx ]) ->
    (forall Bxi ρxi, In (Bxi, ρxi) Bx ->
                exists Bi ρi, In (aconcat (Bxi ^a^ v2) Bi, ρi) B /\
                           (forall x, x ∉ L ->
                                 (Γ ++ [(x, ρxi ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A (Bxi ^a^ v2) ⇒ [(Bi, ρi)]])
    ) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t [: T | A ⇒ B ]
| TEffOp: forall Γ (op: effop) (v2: value) e ρ Ax Bx ρx T A opevent Bi ρi (L: aset),
    is_op_am op v2 opevent ->
    Γ ⊢WF [: T | A ⇒ [(aconcat opevent Bi, ρi)] ] ->
    builtin_typing_relation op (-: ρ ⤑[: ret_ty_of_op op | Ax ⇒ [(Bx, ρx)] ]) ->
    Γ ⊢ v2 ⋮v ρ ->
    (forall x, x ∉ L ->
          (Γ ++ [(x, ρx ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A opevent ⇒ [(Bi, ρi)]]) ->
    Γ ⊢ (tleteffop op v2 e) ⋮t [: T | A ⇒ [(aconcat opevent Bi, ρi)] ]
| TMatchb_true: forall Γ (v: value) e1 e2 τ,
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v (mk_eq_constant true) ->
    Γ ⊢ e1 ⋮t τ ->
    ⌊ Γ ⌋* ⊢t e2 ⋮t ⌊ τ ⌋ ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
| TMatchb_false: forall Γ (v: value) e1 e2 τ,
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v (mk_eq_constant false) ->
    Γ ⊢ e2 ⋮t τ ->
    ⌊ Γ ⌋* ⊢t e1 ⋮t ⌊ τ ⌋ ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
with value_type_check : listctx pty -> tm -> pty -> Prop :=
| TContant: forall Γ (c: constant),
    Γ ⊢WFp (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TVar: forall Γ (x: atom) ρ,
    ctxfind Γ x = Some ρ ->
    Γ ⊢ x ⋮v ρ
| TLam: forall Γ b ρ e T A B (L: aset),
    Γ ⊢WFp (-: ρ ⤑[: T | A ⇒ B ] ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, ρ)]) ⊢ (e ^t^ x) ⋮t ([: T | A ⇒ B ] ^h^ x)) ->
    Γ ⊢ (vlam b e) ⋮v (-: ρ ⤑[: T | A ⇒ B ])
| TLamFix: forall Γ b ρ e T A B (L: aset),
    Γ ⊢WFp (-: ρ ⤑[: T | A ⇒ B ]) ->
    (forall f, f ∉ L -> (Γ ++ [(f, (-: ρ ⤑[: T | A ⇒ B ]))]) ⊢ ((vlam b e) ^v^ f) ⋮v (-: ρ ⤑[: T | A ⇒ B ])) ->
    Γ ⊢ (vfix (⌊ -: ρ ⤑[: T | A ⇒ B ] ⌋) (vlam b e)) ⋮v (-: ρ ⤑[: T | A ⇒ B ])
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' τ" := (value_type_check Γ e τ).

Scheme value_type_check_rec := Induction for value_type_check Sort Prop
    with term_type_check_rec := Induction for term_type_check Sort Prop.

Lemma value_typing_regular: forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋.
Admitted.

Lemma tm_typing_regular: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Admitted.

Lemma well_formed_builtin_typing: forall op ρx A B ρ,
    builtin_typing_relation op (-: ρx ⤑[: ret_ty_of_op op | A ⇒ [(B, ρ)] ]) ->
    forall (v_x: constant), { ∅ }p⟦ ρx ⟧ v_x ->
           forall α, { ∅ }a⟦ A ^a^ v_x ⟧ α ->
                (exists (c: constant), { ∅ }p⟦ ρ ^p^ v_x ⟧ c) /\
                  (forall (c: constant), α +;+ (trevent op v_x) ⇓ c -> { ∅ }p⟦ ρ ^p^ v_x ⟧ c).
Admitted.

Theorem fundamental: forall (Γ: listctx pty) (e: tm) (τ: hty), Γ ⊢ e ⋮t τ -> forall st, ctxRst Γ st -> {st}⟦ τ ⟧ e.
Admitted.
