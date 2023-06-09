From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Denotation.
From CT Require Import Instantiation.

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
Import Instantiation.

(* TODO: wf_am? *)

(** Well-formedness *)
Definition wf_am (Γ: listctx pty) (A: am): Prop := closed_am (ctxdom ⦑ Γ ⦒) A.

Inductive wf_pty: listctx pty -> pty -> Prop :=
| wf_pty_base: forall Γ b ϕ,
    closed_pty (ctxdom ⦑ Γ ⦒) {v: b | ϕ } -> wf_pty Γ {v: b | ϕ }
| wf_pty_arr: forall Γ ρ T A B (L: aset),
    wf_pty Γ ρ ->
    wf_am Γ A ->
    amlist_typed B T ->
    (forall x, x ∉ L ->
          (forall Bi ρi, In (Bi, ρi) B ->
                    wf_pty (Γ ++ [(x, ρ)]) ρi
          )
    ) ->
    wf_pty Γ (-: ρ ⤑[: T | A ⇒ B ]).

Inductive wf_hty: listctx pty -> hty -> Prop :=
| wf_hty_: forall Γ T A B,
    amlist_typed B T ->
    (forall Ai ρi, In (Ai, ρi) B -> wf_am Γ Ai /\ wf_pty Γ ρi) ->
    wf_hty Γ [: T | A ⇒ B ].

Notation " Γ '⊢WF' τ " := (wf_hty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFp' τ " := (wf_pty Γ τ) (at level 20, τ constr, Γ constr).

Definition subtyping (Γ: listctx pty) (τ1 τ2: hty) : Prop :=
  (* Assume [τ1] and [τ2] are valid [hty]s. *)
  forall Γv, ctxRst Γ Γv -> forall v,⟦(m{ Γv }h) τ1⟧ ((m{ Γv }v) v) → ⟦(m{ Γv }h) τ2⟧ ((m{ Γv }v) v).

Notation " Γ '⊢' τ1 '⪡' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ"  (at level 20).


Definition A_ρa_B_ρb_list_A_ρa (l: list (am * pty) ) (tril: list (am * pty * am * pty)) :=
  forall A ρa, In (A, ρa) l <-> (exists B ρb, In (A, ρa, B, ρb) tril).

Definition A_ρa_B_ρb_list_AB_ρb (l: list (am * pty) ) (tril: list (am * pty * am * pty)) :=
  forall A B ρb, In (aconcat A B, ρb) l <-> (exists ρa, In (A, ρa, B, ρb) tril).

(** Typing *)
Inductive term_type_check : listctx pty -> tm -> hty -> Prop :=
| TValue: forall Γ v ρ,
    Γ ⊢ v ⋮v ρ ->
    Γ ⊢ v ⋮t (pty_to_rty ρ)
| TSub: forall Γ e (τ1 τ2: hty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 -> Γ ⊢ τ1 ⪡ τ2 -> (Γ ⊢ e ⋮t τ2)
| TLetE: forall Γ e_x e Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ (L: aset),
    Γ ⊢WF [: T | A ⇒ BxB_ρ ] ->
    Γ ⊢ e_x ⋮t [: Tx | A ⇒ Bx_ρx ] ->
    A_ρa_B_ρb_list_A_ρa Bx_ρx Bx_ρx_B_ρ ->
    A_ρa_B_ρb_list_AB_ρb BxB_ρ Bx_ρx_B_ρ ->
    (forall x, x ∉ L ->
          forall Bxi ρxi Bi ρi,
            In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ ->
            (Γ ++ [(x, ρxi)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A Bxi ⇒ [(Bi, ρi)]]) ->
    Γ ⊢ (tlete e_x e) ⋮t [: T | A ⇒ BxB_ρ ]
| TApp: forall Γ (v1 v2: value) e ρ Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ (L: aset),
    Γ ⊢WF [: T | A ⇒ BxB_ρ ] ->
    Γ ⊢ v2 ⋮v ρ ->
    Γ ⊢ v1 ⋮v (-: ρ ⤑[: Tx | astar ∘ ⇒ Bx_ρx ]) ->
    A_ρa_B_ρb_list_A_ρa Bx_ρx Bx_ρx_B_ρ ->
    A_ρa_B_ρb_list_AB_ρb BxB_ρ Bx_ρx_B_ρ ->
    (forall x, x ∉ L ->
          forall Bxi ρxi Bi ρi,
            In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ ->
            (Γ ++ [(x, ρxi ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A (Bxi ^a^ v2) ⇒ [(Bi, ρi)]]) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t [: T | A ⇒ BxB_ρ ]
| TEffOp: forall Γ (op: effop) (v2: value) e ρ A Bx ϕx T opevent Bi ρi (L: aset),
    is_op_am op v2 ϕx opevent ->
    Γ ⊢WF [: T | A ⇒ [(aconcat opevent Bi, ρi)] ] ->
    builtin_typing_relation op (-: ρ ⤑[: ret_ty_of_op op | A ⇒ [(Bx, {v: ret_ty_of_op op | ϕx})] ]) ->
    Γ ⊢ v2 ⋮v ρ ->
    (forall x, x ∉ L ->
          (Γ ++ [(x, ({v: ret_ty_of_op op | ϕx}) ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A opevent ⇒ [(Bi, ρi)]]) ->
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
with value_type_check : listctx pty -> value -> pty -> Prop :=
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
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋ /\ wf_pty Γ ρ.
Admitted.

Lemma tm_typing_regular: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋ /\ wf_hty Γ τ.
Admitted.

Lemma well_formed_builtin_typing: forall op ρx A B ρ,
    builtin_typing_relation op (-: ρx ⤑[: ret_ty_of_op op | A ⇒ [(B, ρ)] ]) ->
    forall (v_x: constant), p⟦ ρx ⟧ v_x ->
                       forall α, a⟦ A ^a^ v_x ⟧ α ->
                            (exists (c: constant), p⟦ ρ ^p^ v_x ⟧ c) /\
                              (forall (c: constant), app{op, v_x}⇓{ α } c -> p⟦ ρ ^p^ v_x ⟧ c).
Admitted.

Lemma reduction_tlete:  forall e_x e α β v,
    α ⊧ tlete e_x e ↪*{ β } v <->
    (exists (βx βe: trace) (v_x: value),
      β = βx +;+ βe /\ α ⊧ e_x ↪*{ βx } v_x /\ α +;+ βx ⊧ (e ^t^ v_x) ↪*{ βe } v).
Admitted.

(* I have proved this lemma in Poirot. *)
Lemma msubst_open: forall (Γv: env) e (v_x: value) (x: atom),
    x # (dom Γv ∪ stale e ∪ stale v_x) ->
    (m{Γv}t) e ^t^ v_x = (m{<[x:=v_x]> Γv}t) (e ^t^ x).
Admitted.

Lemma msubst_hty: forall (Γv: env) T A B, m{Γv}h [:T|A⇒B] = [:T|m{Γv}a A ⇒ m{Γv}pa B].
Admitted.

Lemma msubst_lete: forall (Γv: env) e_x e, (m{Γv}t (tlete e_x e) = tlete ((m{Γv}t) e_x) ((m{Γv}t) e)).
Admitted.

Lemma msubst_concat: forall (Γv: env) A1 A2, m{Γv}a (aconcat A1 A2) = (aconcat (m{Γv}a A1) (m{Γv}a A2)).
Admitted.

Lemma msubst_amlist_typed: forall (Γv: env) B T,
    amlist_typed ((m{Γv}pa) B) T <-> amlist_typed B T.
Admitted.

Lemma in_msubst: forall (Γv: env) (A: am) (ρ: pty) (B: list (am * pty)),
    In (A, ρ) (m{Γv}pa B) <-> exists A' ρ', A = m{Γv}a A' /\ ρ = m{Γv}p ρ' /\ In (A', ρ') B.
Admitted.

Definition subst4 Γv (x: am * pty * am * pty) :=
  match x with
    | (A, ρa, B, ρb) => (m{Γv}a A, m{Γv}p ρa, m{Γv}a B, m{Γv}p ρb)
  end.

Lemma in_msubst4: forall (Γv: env) (A1: am) (ρ1: pty) (A2: am) (ρ2: pty) (B4: list (am * pty * am * pty)),
    In (A1, ρ1, A2, ρ2) (List.map (subst4 Γv) B4) ->
    exists A1' ρ1' A2' ρ2',
      A1 = m{Γv}a A1' /\ ρ1 = m{Γv}p ρ1' /\ A2 = m{Γv}a A2' /\ ρ2 = m{Γv}p ρ2' /\ In (A1', ρ1', A2', ρ2') B4.
Admitted.

Lemma am_concat: forall A B α β,
  (a⟦A⟧) α -> (a⟦B⟧) β -> (a⟦ aconcat A B ⟧) (α +;+ β).
Admitted.

Lemma am_denotation_fv: forall Γv x v_x A,
    x ∉ stale A -> forall α, a⟦(m{<[x:=v_x]> Γv}a) A⟧ α <-> a⟦(m{Γv}a) A⟧ α.
Admitted.

Lemma msubst_fv {T: Type} `{@Stale aset T} : forall (Γv: env) (x: atom) (v_x: value)
                             (f_subst: atom -> value -> T -> T)
                             (e: T),
    x # stale e ->
    msubst f_subst (<[x:=v_x]> Γv) e = msubst f_subst Γv e.
Admitted.

Lemma in_singleton {T1 T2: Type}: forall (a1 a1': T1) (a2 a2': T2), In (a1, a2) [(a1', a2')] -> a1 = a1' /\ a2 = a2'.
Proof.
  intros. inversion H. inversion H0; subst; auto. inversion H0.
Qed.

Theorem fundamental: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ ->
    (* NOTE: [τ] being valid should be a regularity lemma. *)
    forall Γv, ctxRst Γ Γv -> ⟦ msubst hty_subst Γv τ ⟧ (msubst tm_subst Γv e).
Proof.
  apply (term_type_check_rec
           (* NOTE: should this be the denotation of [pty]? *)
           (fun Γ (v: value) ρ _ =>
              forall Γv, ctxRst Γ Γv -> ⟦ m{Γv}h (pty_to_rty ρ) ⟧ (m{Γv}v v))
           (fun Γ e (τ: hty) _ =>
              forall Γv, ctxRst Γ Γv -> ⟦ m{Γv}h τ ⟧ (m{Γv}t e))
        ).
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros Γ e_x e Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ L HWFBρ HTe_x HDe_x Hin1 Hin2 _ He Γv HΓv.
    auto_pose_fv x. repeat specialize_with x. rewrite msubst_lete.
    rewrite msubst_hty.
    simpl. intros HBtyped α β v HDα Hstepv.
    rewrite reduction_tlete in Hstepv. destruct Hstepv as (βx & βe & v_x & Htmp & Hstepv_x & Hstepv). subst.
    rewrite msubst_open with (x:=x) in Hstepv. 2: { admit. }
    specialize (HDe_x _ HΓv). rewrite msubst_hty in HDe_x.
    assert (amlist_typed ((m{Γv}pa) Bx_ρx) Tx) as HH1. { rewrite msubst_amlist_typed. admit. }
    specialize (HDe_x HH1 _ _ _ HDα Hstepv_x).
    destruct HDe_x as (Bxi' & ρxi' & HinBx_ρx & Hβx & Hv_x).
    apply in_msubst in HinBx_ρx. destruct HinBx_ρx as (Bxi & ρxi & Htmp0 & Htmp1 & HinBx_ρx); subst.
    apply Hin1 in HinBx_ρx. destruct HinBx_ρx as (Bi & ρi & Hin). clear Hin1.
    assert (ctxRst (Γ ++ [(x, ρxi)]) (<[x:=v_x]> Γv)) as HH2. { constructor; auto. admit. }
    specialize (He _ _ _ _ Hin (<[ x := v_x]> Γv) HH2). rewrite msubst_hty in He.
    assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, ρi)]) T) as HH3. { rewrite msubst_amlist_typed. admit. }
    specialize (He HH3 (α +;+ βx) βe v).
    assert (x ∉ stale Bxi). admit.
    assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat A Bxi)⟧) (α +;+ βx)) as Hconcat.
    { rewrite am_denotation_fv; try fast_set_solver. rewrite msubst_concat.
      apply am_concat; auto. }
    specialize (He Hconcat Hstepv). destruct He as (Bi'' & ρi'' & Hini & Hβe & Hv).
    apply in_msubst in Hini. destruct Hini as (Bi' & ρi' & Htmp0 & Htmp1 & Hini); subst.
    apply in_singleton in Hini. mydestr; subst.
    assert (In ((aconcat Bxi Bi), ρi) BxB_ρ) as Hinii. { apply Hin2. eauto. }
    exists (m{<[x:=v_x]> Γv}a (aconcat Bxi Bi)), (m{<[x:=v_x]> Γv}p ρi).
    repeat split.
    + rewrite in_msubst. exists (aconcat Bxi Bi), ρi. repeat split; auto.
      * rewrite msubst_fv; auto. admit.
      * rewrite msubst_fv; auto. admit.
    + rewrite msubst_concat. apply am_concat; auto. rewrite am_denotation_fv; auto.
Admitted.
