From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
(* Import Substitution. *)
Import Qualifier.
Import ListCtx.
Import List.

(** * We define the refinement type in locally nameless style. *)

Inductive am : Type :=
(** bvar 1 is argument, bvar 0 is result value *)
| aevent (op: effop) (ϕ: qualifier)
(* □⟨⊤⟩ in the paper, directly encoded as a primitive operator here for
convenience. *)
| aany
| aconcat (a: am) (b: am)
(* We only need the operations above for metatheory. Other connectives or
modality can be added, but not interesting. *)
| aunion (a: am) (b: am)
.

Notation "'⟨' op '|' ϕ '⟩'" := (aevent op ϕ) (at level 5, format "⟨ op | ϕ ⟩", op constr, ϕ constr).
Notation " a ';+' b " := (aconcat a b) (at level 5, format "a ;+ b", b constr, a constr, right associativity).
Notation "∘*" := aany (at level 5).

Inductive pty : Type :=
| basepty (B: base_ty) (ϕ: qualifier)
| arrpty (ρ: pty) (τ: hty)
| ghostpty (B: base_ty) (ρ: pty)

with hty : Type :=
| hoarehty (ρ: pty) (pre post: am)
| interhty (τ1 τ2: hty).

Scheme pty_hty_rect := Induction for pty Sort Type
    with hty_pty_rect := Induction for hty Sort Type.
Combined Scheme pty_hty_mutrect from pty_hty_rect, hty_pty_rect.

Global Hint Constructors hty: core.
Global Hint Constructors pty: core.
Global Hint Constructors am: core.

Notation "'{:' B '|' ϕ '}'" := (basepty B ϕ) (at level 5, format "{: B | ϕ }", B constr, ϕ constr).
Notation "ρ '⇨' τ " :=
 (arrpty ρ τ) (at level 80, format "ρ ⇨ τ", right associativity, ρ constr, τ constr).
Notation "B '⇢' ρ " :=
 (ghostpty B ρ) (at level 80, format "B ⇢ ρ", right associativity, B constr, ρ constr).
Notation "'[:' ρ '|' a '▶' b ']'" := (hoarehty ρ a b) (at level 5, format "[: ρ | a ▶ b ]", ρ constr, a constr, b constr).
Notation "τ1 '⊓' τ2" := (interhty τ1 τ2).

(** Erase *)

Fixpoint pty_erase ρ : ty :=
  match ρ with
  | {: B | _} => B
  | ρ ⇨ τ => (pty_erase ρ) ⤍ (hty_erase τ)
  | B ⇢ ρ => pty_erase ρ
  end

with hty_erase τ : ty :=
  match τ with
  | [: ρ | _ ▶ _ ] => pty_erase ρ
  | τ1 ⊓ τ2 => hty_erase τ1
  end.

Class Erase A := erase : A -> ty.
#[global]
  Instance pty_erase_ : Erase pty := pty_erase.
#[global]
  Instance hty_erase_ : Erase hty := hty_erase.

Notation " '⌊' ty '⌋' " := (erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

(** free variables *)

Fixpoint am_fv a : aset :=
  match a with
  | aevent _ ϕ => qualifier_fv ϕ
  | aany => ∅
  | aconcat a b | aunion a b => am_fv a ∪ am_fv b
  end.

Fixpoint pty_fv ρ : aset :=
  match ρ with
  | {: _ | ϕ } => qualifier_fv ϕ
  | ρ ⇨ τ => pty_fv ρ ∪ hty_fv τ
  | _ ⇢ ρ => pty_fv ρ
  end

with hty_fv τ : aset :=
  match τ with
  | [: ρ | a ▶ b ] => pty_fv ρ ∪ am_fv a ∪ am_fv b
  | τ1 ⊓ τ2 => hty_fv τ1 ∪ hty_fv τ2
  end.

#[global]
  Instance pty_stale : @Stale aset pty := pty_fv.
Arguments pty_stale /.
#[global]
  Instance am_stale : @Stale aset am := am_fv.
Arguments am_stale /.
#[global]
  Instance hty_stale : @Stale aset hty := hty_fv.
Arguments hty_stale /.

(* The effect operator always has 2 bound variables *)
Fixpoint am_open (k: nat) (s: value) (a : am): am :=
  match a with
  | aevent op ϕ => aevent op (qualifier_open (S (S k)) s ϕ)
  | aany => aany
  | aconcat a b => aconcat (am_open k s a) (am_open k s b)
  | aunion a b => aunion (am_open k s a) (am_open k s b)
  end.

Fixpoint pty_open (k: nat) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {: B | ϕ } => {: B | qualifier_open (S k) s ϕ }
  | ρ ⇨ τ => (pty_open k s ρ) ⇨ (hty_open (S k) s τ)
  | B ⇢ ρ => B ⇢ (pty_open (S k) s ρ)
  end

with hty_open (k: nat) (s: value) (τ : hty): hty :=
  match τ with
  | [: ρ | a ▶ b ] => [: (pty_open k s ρ) | (am_open k s a) ▶ (am_open k s b)]
  | τ1 ⊓ τ2 => (hty_open k s τ1) ⊓ (hty_open k s τ2)
  end.

Notation "'{' k '~p>' s '}' e" := (pty_open k s e) (at level 20, k constr).
Notation "'{' k '~a>' s '}' e" := (am_open k s e) (at level 20, k constr).
Notation "'{' k '~h>' s '}' e" := (hty_open k s e) (at level 20, k constr).
Notation "e '^p^' s" := (pty_open 0 s e) (at level 20).
Notation "e '^a^' s" := (am_open 0 s e) (at level 20).
Notation "e '^h^' s" := (hty_open 0 s e) (at level 20).

Fixpoint am_subst (k: atom) (s: value) (a : am): am :=
  match a with
  | aevent op ϕ => aevent op (qualifier_subst k s ϕ)
  | aany => aany
  | aconcat a b => aconcat (am_subst k s a) (am_subst k s b)
  | aunion a b => aunion (am_subst k s a) (am_subst k s b)
  end.

Fixpoint pty_subst (k: atom) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {: B | ϕ } => {: B | qualifier_subst k s ϕ }
  | ρ ⇨ τ => (pty_subst k s ρ) ⇨ (hty_subst k s τ)
  | B ⇢ ρ => B ⇢ (pty_subst k s ρ)
  end

with hty_subst (k: atom) (s: value) (τ : hty): hty :=
  match τ with
  | [: ρ | a ▶ b ] => [: (pty_subst k s ρ) | am_subst k s a ▶ (am_subst k s b)]
  | τ1 ⊓ τ2 => (hty_subst k s τ1) ⊓ (hty_subst k s τ2)
  end.

Notation "'{' x ':=' s '}p'" := (pty_subst x s) (at level 20, format "{ x := s }p", x constr).
Notation "'{' x ':=' s '}a'" := (am_subst x s) (at level 20, format "{ x := s }a", x constr).
Notation "'{' x ':=' s '}h'" := (hty_subst x s) (at level 20, format "{ x := s }h", x constr).

(** well formed, locally closed, closed with state *)

Inductive lc_am : am -> Prop :=
| lc_aevent: forall op ϕ (L : aset),
    (* This is quite annoying. *)
    (forall (x : atom), x ∉ L -> forall (y : atom), y ∉ L -> lc_qualifier ({0 ~q> y} ({1 ~q> x} ϕ))) ->
    lc_am (aevent op ϕ)
| lc_aany : lc_am aany
| lc_aconcat : forall a b, lc_am a -> lc_am b -> lc_am (aconcat a b)
| lc_aunion : forall a b, lc_am a -> lc_am b -> lc_am (aunion a b)
.

Inductive lc_pty : pty -> Prop :=
| lc_pty_base: forall B ϕ (L : aset),
    (forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) ->
    lc_pty {: B | ϕ }
| lc_pty_arr: forall ρ τ (L : aset),
    lc_pty ρ ->
    (forall x : atom, x ∉ L -> lc_hty (τ ^h^ x)) ->
    lc_pty (ρ ⇨ τ)
| lc_pty_ghost: forall B ρ (L : aset),
    (forall x : atom, x ∉ L -> lc_pty (ρ ^p^ x)) ->
    lc_pty (B ⇢ ρ)

with lc_hty : hty -> Prop :=
| lc_hty_hoare : forall ρ a b,
    lc_pty ρ ->
    lc_am a ->
    lc_am b ->
    lc_hty [: ρ | a ▶ b ]
| lc_hty_inter : forall τ1 τ2,
    lc_hty τ1 ->
    lc_hty τ2 ->
    lc_hty (τ1 ⊓ τ2).

Scheme lc_pty_hty_ind := Minimality for lc_pty Sort Prop
    with lc_hty_pty_ind := Minimality for lc_hty Sort Prop.
Combined Scheme lc_pty_hty_mutind from lc_pty_hty_ind, lc_hty_pty_ind.

Inductive closed_am (d: aset) (a: am): Prop :=
| closed_am_: lc_am a -> am_fv a ⊆ d -> closed_am d a.

Inductive closed_pty (d : aset) (ρ: pty): Prop :=
| closed_pty_: lc_pty ρ -> pty_fv ρ ⊆ d -> closed_pty d ρ.

Inductive closed_hty (d: aset) (ρ: hty): Prop :=
| closed_hty_: lc_hty ρ -> hty_fv ρ ⊆ d -> closed_hty d ρ.

(* Type context *)

Inductive ok_ctx: listctx pty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx pty)(x: atom) (ρ: pty),
    ok_ctx Γ ->
    closed_pty (ctxdom Γ) ρ ->
    x ∉ ctxdom Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

Definition ctx_erase (Γ: listctx pty) :=
  ⋃ ((List.map (fun e => {[e.1 := pty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** Ty Function *)
Definition mk_eq_constant c := {: ty_of_const c | b0:c= c }.
Definition mk_bot ty := {: ty | mk_q_under_bot }.
Definition mk_top ty := {: ty | mk_q_under_top }.
Definition mk_eq_var ty (x: atom) := {: ty | b0:x= x }.

Lemma pty_erase_open_eq ρ k s :
  pty_erase ρ = pty_erase ({k ~p> s} ρ)
with hty_erase_open_eq τ k s :
  hty_erase τ = hty_erase ({k ~h> s} τ).
Proof.
  destruct ρ; simpl; eauto; f_equal; eauto.
  destruct τ; simpl; eauto.
Qed.

Lemma pty_erase_subst_eq ρ x s :
  pty_erase ρ = pty_erase ({x := s}p ρ)
with hty_erase_subst_eq τ x s :
  hty_erase τ = hty_erase ({x := s}h τ).
Proof.
  destruct ρ; simpl; eauto; f_equal; eauto.
  destruct τ; simpl; eauto.
Qed.

Lemma ctx_erase_lookup Γ x ρ :
  ctxfind Γ x = Some ρ ->
  ⌊Γ⌋* !! x = Some ⌊ρ⌋.
Proof.
  induction Γ; simpl; intros; try easy.
  destruct a. case_decide. simplify_eq.
  cbn. simplify_map_eq. reflexivity.
  simp_hyps.
  cbn. rewrite insert_empty. rewrite <- insert_union_singleton_l.
  simplify_map_eq. reflexivity.
Qed.

Lemma ctx_erase_app Γ Γ':
  ⌊Γ ++ Γ'⌋* = ⌊Γ⌋* ∪ ⌊Γ'⌋*.
Proof.
  induction Γ; simpl.
  - cbn. by rewrite map_empty_union.
  - destruct a. unfold ctx_erase in *. cbn. rewrite IHΓ.
    by rewrite map_union_assoc.
Qed.

Lemma ctx_erase_dom Γ :
  dom ⌊Γ⌋* ≡ ctxdom Γ.
Proof.
  induction Γ; simpl.
  - cbn. apply dom_empty.
  - destruct a. cbn in *.
    rewrite insert_empty.
    setoid_rewrite dom_union.
    rewrite dom_singleton.
    f_equiv. eauto.
Qed.

Lemma ctx_erase_app_r Γ x ρ :
  x # Γ ->
  ⌊Γ ++ [(x, ρ)]⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  rewrite ctx_erase_app.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_r. auto.
  simpl in H. rewrite <- ctx_erase_dom in H.
  by apply not_elem_of_dom.
Qed.

Lemma subst_commute_am : forall x u_x y u_y a,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }a ({y := u_y }a a) = {y := u_y }a ({x := u_x }a a).
Proof.
  intros.
  induction a; simpl; eauto; f_equal; eauto using subst_commute_qualifier.
Qed.

Lemma subst_commute_pty : forall x u_x y u_y ρ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }p ({y := u_y }p ρ) = {y := u_y }p ({x := u_x }p ρ)
with subst_commute_hty : forall x u_x y u_y τ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }h ({y := u_y }h τ) = {y := u_y }h ({x := u_x }h τ).
Proof.
  destruct ρ; simpl; intros; f_equal;
    eauto using subst_commute_qualifier, subst_commute_am.
  destruct τ; simpl; intros; f_equal;
    eauto using subst_commute_qualifier, subst_commute_am.
Qed.

Lemma subst_fresh_am: forall (a: am) (x:atom) (u: value),
    x # a -> {x := u}a a = a.
Proof.
  intros. induction a; simpl in *; eauto; repeat f_equal;
    eauto using subst_fresh_qualifier;
    auto_apply; try my_set_solver.
Qed.

Lemma subst_fresh_pty: forall (ρ: pty) (x:atom) (u: value),
    x # ρ -> {x := u}p ρ = ρ
with subst_fresh_hty: forall (τ: hty) (x:atom) (u: value),
    x # τ -> {x := u}h τ = τ.
Proof.
  destruct ρ; simpl; intros; f_equal; eauto using subst_fresh_qualifier;
    auto_apply; my_set_solver.
  destruct τ; simpl; intros; f_equal;
    solve [ auto_apply; my_set_solver
          | apply subst_fresh_am; my_set_solver ].
Qed.

Lemma open_fv_am (a : am) (v : value) k :
  am_fv ({k ~a> v} a) ⊆ am_fv a ∪ fv_value v.
Proof.
  induction a; simpl; eauto using open_fv_qualifier;
    repeat my_set_solver.
Qed.

Lemma open_fv_am' (a : am) (v : value) k :
  am_fv a ⊆ am_fv ({k ~a> v} a).
Proof.
  induction a; simpl; eauto using open_fv_qualifier';
    my_set_solver.
Qed.

Lemma open_fv_pty (ρ : pty) (v : value) k :
  pty_fv ({k ~p> v} ρ) ⊆ pty_fv ρ ∪ fv_value v
with open_fv_hty (τ : hty) (v : value) k :
  hty_fv ({k ~h> v} τ) ⊆ hty_fv τ ∪ fv_value v.
Proof.
  all: revert k.
  destruct ρ; simpl; intros; eauto using open_fv_qualifier.
  etrans. apply union_mono; eauto. my_set_solver.
  destruct τ; simpl; intros.
  etrans. repeat apply union_mono; eauto using open_fv_am. my_set_solver.
  etrans. repeat apply union_mono; eauto. my_set_solver.
Qed.

Lemma open_fv_pty' (ρ : pty) (v : value) k :
  pty_fv ρ ⊆ pty_fv ({k ~p> v} ρ)
with open_fv_hty' (τ : hty) (v : value) k :
  hty_fv τ ⊆ hty_fv ({k ~h> v} τ).
Proof.
  all: revert k.
  destruct ρ; simpl; intros; eauto using open_fv_qualifier';
    repeat apply union_mono; eauto.
  destruct τ; simpl; intros;
    repeat apply union_mono; eauto using open_fv_am'.
Qed.

Lemma open_subst_same_qualifier: forall x y (ϕ : qualifier) k,
    x # ϕ ->
    {x := y }q ({k ~q> x} ϕ) = {k ~q> y} ϕ.
Proof.
  destruct ϕ. cbn. intros.
  f_equal. clear - H.
  (* A better proof should simply reduce to vector facts. Don't bother yet. *)
  induction vals; cbn; eauto.
  cbn in H.
  f_equal. apply open_subst_same_value. my_set_solver.
  apply IHvals. my_set_solver.
Qed.

Lemma open_subst_same_am: forall x y (a : am) k,
    x # a ->
    {x := y }a ({k ~a> x} a) = {k ~a> y} a.
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using open_subst_same_qualifier.
  all:
  repeat
    match goal with
    | H : forall k, _ # _ -> _ =_ |- _ => rewrite H by my_set_solver; eauto
    end.
Qed.

Lemma not_in_union_list {A C} `{SemiSet A C} (x : A) (ss : list C):
  x ∉ ⋃ ss ->
  forall s, In s ss -> x ∉ s.
Proof.
  induction ss; cbn; intros; eauto.
  qsimpl.
Qed.

Lemma open_subst_same_pty: forall x y (ρ : pty) k,
    x # ρ ->
    {x := y }p ({k ~p> x} ρ) = {k ~p> y} ρ
with open_subst_same_hty: forall x y (τ : hty) k,
    x # τ ->
    {x := y }h ({k ~h> x} τ) = {k ~h> y} τ.
Proof.
  destruct ρ; simpl; intros; f_equal; eauto using open_subst_same_qualifier;
    auto_apply; my_set_solver.
  destruct τ; simpl; intros; f_equal;
    solve [ auto_apply; my_set_solver
          | apply open_subst_same_am; my_set_solver ].
Qed.

Lemma subst_open_qualifier: forall (ϕ: qualifier) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}q ({k ~q> u} ϕ) = ({k ~q> {x := w}v u} ({x := w}q ϕ)).
Proof.
  destruct ϕ. cbn. intros.
  f_equal.
  rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using subst_open_value.
Qed.

Lemma subst_open_am: forall (a: am) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}a ({k ~a> u} a) = ({k ~a> {x := w}v u} ({x := w}a a)).
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using subst_open_qualifier.
  all:
  repeat
    match goal with
    | H : context [lc _ -> _] |- _ => rewrite H by my_set_solver; eauto
    end.
Qed.

Lemma subst_open_pty: forall (ρ: pty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}p ({k ~p> u} ρ) = ({k ~p> {x := w}v u} ({x := w}p ρ))
with subst_open_hty: forall (τ: hty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}h ({k ~h> u} τ) = ({k ~h> {x := w}v u} ({x := w}h τ)).
Proof.
  destruct ρ; simpl; intros; f_equal; eauto using subst_open_qualifier.
  destruct τ; simpl; intros; f_equal; eauto using subst_open_am.
Qed.

Lemma subst_open_qualifier_closed:
  ∀ (ϕ : qualifier) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }q ({k ~q> u} ϕ) = {k ~q> u} ({x := w }q ϕ).
Proof.
  intros. rewrite subst_open_qualifier; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_pty_closed:
  ∀ (ρ : pty) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }p ({k ~p> u} ρ) = {k ~p> u} ({x := w }p ρ).
Proof.
  intros. rewrite subst_open_pty; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_am_closed:
  ∀ (a : am) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }a ({k ~a> u} a) = {k ~a> u} ({x := w }a a).
Proof.
  intros. rewrite subst_open_am; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_hty_closed:
  ∀ (τ : hty) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }h ({k ~h> u} τ) = {k ~h> u} ({x := w }h τ).
Proof.
  intros. rewrite subst_open_hty; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_lc_qualifier : forall x (u: value) (ϕ: qualifier),
    lc_qualifier ϕ -> lc u -> lc_qualifier ({x := u}q ϕ).
Proof.
  destruct 1. intros Hu.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map.
  rewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. eauto using subst_lc_value.
Qed.

Lemma subst_open_var_qualifier: forall x y (u: value) (ϕ: qualifier) (k: nat),
    x <> y -> lc u -> {x := u}q ({k ~q> y} ϕ) = ({k ~q> y} ({x := u}q ϕ)).
Proof.
  intros.
  rewrite subst_open_qualifier; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_am: forall x y (u: value) (a: am) (k: nat),
    x <> y -> lc u -> {x := u}a ({k ~a> y} a) = ({k ~a> y} ({x := u}a a)).
Proof.
  intros.
  rewrite subst_open_am; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_pty: forall x y (u: value) (ρ: pty) (k: nat),
    x <> y -> lc u -> {x := u}p ({k ~p> y} ρ) = ({k ~p> y} ({x := u}p ρ)).
Proof.
  intros.
  rewrite subst_open_pty; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_hty: forall x y (u: value) (τ: hty) (k: nat),
    x <> y -> lc u -> {x := u}h ({k ~h> y} τ) = ({k ~h> y} ({x := u}h τ)).
Proof.
  intros.
  rewrite subst_open_hty; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_lc_am : forall x (u: value) (a: am),
    lc_am a -> lc u -> lc_am ({x := u}a a).
Proof.
  induction 1; intros Hu; eauto using lc_am.
  econstructor.
  auto_exists_L_intros.
  specialize_with x0.
  specialize_with y.
  rewrite <- !subst_open_var_qualifier by (eauto; my_set_solver).
  eauto using subst_lc_qualifier.
Qed.

Lemma subst_lc_pty : forall x (u: value) (ρ: pty),
    lc_pty ρ -> lc u -> lc_pty ({x := u}p ρ)
with subst_lc_hty : forall x (u: value) (τ: hty),
    lc_hty τ -> lc u -> lc_hty ({x := u}h τ).
Proof.
  all: destruct 1; intros; simpl; econstructor; eauto using subst_lc_am;
    instantiate_atom_listctx.
  - rewrite <- subst_open_var_qualifier by (eauto; my_set_solver);
      eauto using subst_lc_qualifier.
  - rewrite <- subst_open_var_hty by (eauto; my_set_solver); eauto.
  - rewrite <- subst_open_var_pty by (eauto; my_set_solver); eauto.
Qed.

Lemma fv_of_subst_qualifier_closed:
  forall x (u : value) (ϕ: qualifier),
    closed_value u ->
    qualifier_fv ({x := u }q ϕ) = qualifier_fv ϕ ∖ {[x]}.
Proof.
  destruct ϕ; simpl. clear. induction vals; simpl; intros.
  my_set_solver.
  rewrite fv_of_subst_value_closed by eauto.
  my_set_solver.
Qed.

Lemma fv_of_subst_am_closed:
  forall x (u : value) (a: am),
    closed_value u ->
    am_fv ({x := u }a a) = (am_fv a ∖ {[x]}).
Proof.
  induction a; simpl; eauto using fv_of_subst_qualifier_closed; my_set_solver.
Qed.

Lemma fv_of_subst_pty_closed:
  forall x (u : value) (ρ: pty),
    closed_value u ->
    pty_fv ({x := u }p ρ) = (pty_fv ρ ∖ {[x]})
with fv_of_subst_hty_closed:
  forall x (u : value) (τ: hty),
    closed_value u ->
    hty_fv ({x := u }h τ) = (hty_fv τ ∖ {[x]}).
Proof.
  destruct ρ; simpl; intros; eauto using fv_of_subst_qualifier_closed.
  rewrite !fv_of_subst_hty_closed, !fv_of_subst_pty_closed by eauto.
  my_set_solver.
  destruct τ; simpl; intros.
  rewrite !fv_of_subst_am_closed, !fv_of_subst_pty_closed by eauto.
  my_set_solver.
  rewrite !fv_of_subst_hty_closed by eauto.
  my_set_solver.
Qed.

Lemma open_not_in_eq_qualifier (x : atom) (ϕ : qualifier) k :
  x # {k ~q> x} ϕ ->
  forall e, ϕ = {k ~q> e} ϕ.
Proof.
  destruct ϕ. simpl. intros.
  f_equal.
  clear - H.
  induction vals; simpl; eauto.
  f_equal. apply open_not_in_eq_value with x. my_set_solver.
  auto_apply. my_set_solver.
Qed.

Lemma open_not_in_eq_am (x : atom) (a : am) k :
  x # {k ~a> x} a ->
  forall e, a = {k ~a> e} a.
Proof.
  induction a; simpl; intros; eauto.
  f_equal. eapply open_not_in_eq_qualifier. my_set_solver.
  all: f_equal; auto_apply; my_set_solver.
Qed.

Lemma open_not_in_eq_pty (x : atom) (ρ : pty) k :
  x # {k ~p> x} ρ ->
  forall e, ρ = {k ~p> e} ρ
with open_not_in_eq_hty (x : atom) (τ : hty) k :
  x # {k ~h> x} τ ->
  forall e, τ = {k ~h> e} τ.
Proof.
  all: revert k; specialize (open_not_in_eq_pty x); specialize (open_not_in_eq_hty x).
  destruct ρ; simpl; intros; f_equal; eauto using open_not_in_eq_qualifier;
    auto_apply; my_set_solver.
  destruct τ; simpl; intros; f_equal;
    solve [ auto_apply; my_set_solver
          | apply (open_not_in_eq_am x); my_set_solver ].
Qed.

Lemma subst_intro_pty: forall (ρ: pty) (x:atom) (w: value) (k: nat),
    x # ρ ->
    lc w -> {x := w}p ({k ~p> x} ρ) = ({k ~p> w} ρ).
Proof.
  intros.
  specialize (subst_open_pty ρ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_pty; auto.
Qed.

Lemma lc_subst_qualifier:
  forall x (u: value) (ϕ: qualifier), lc_qualifier ({x := u}q ϕ) -> lc u -> lc_qualifier ϕ.
Proof.
  intros.
  sinvert H.
  destruct ϕ. simpl in *. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  srewrite Vector.to_list_map.
  srewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. eauto using lc_subst_value.
Qed.

Lemma lc_subst_am:
  forall x (u: value) (a: am), lc_am ({x := u}a a) -> lc u -> lc_am a.
Proof.
  intros.
  remember (({x:=u}a) a).
  generalize dependent a.
  induction H; intros;
      match goal with
      | H : _ = {_:=_}a ?a |- _ => destruct a; simpl in *; simplify_eq
      end; eauto using lc_am.
  econstructor.
  auto_exists_L_intros. specialize_with x0. specialize_with y.
  rewrite <- !subst_open_var_qualifier in H by (eauto; my_set_solver).
  eauto using lc_subst_qualifier.
Qed.

Lemma lc_subst_pty: forall x (u: value) (ρ: pty), lc_pty ({x := u}p ρ) -> lc u -> lc_pty ρ
with lc_subst_hty: forall x (u: value) (τ: hty), lc_hty ({x := u}h τ) -> lc u -> lc_hty τ.
Proof.
  intros.
  remember (({x:=u}p) ρ).
  generalize dependent ρ.
  destruct H; intros ρ' **; destruct ρ'; simpl in *; simplify_eq;
    econstructor; eauto;
    instantiate_atom_listctx.
  rewrite <- subst_open_var_qualifier in * by (eauto; my_set_solver);
    eauto using lc_subst_qualifier.
  rewrite <- subst_open_var_hty in * by (eauto; my_set_solver); eauto.
  rewrite <- subst_open_var_pty in * by (eauto; my_set_solver); eauto.

  intros.
  remember (({x:=u}h) τ).
  generalize dependent τ.
  destruct H; intros τ' **; destruct τ'; simpl in *; simplify_eq;
    econstructor; eauto using lc_subst_am.
Qed.

Lemma open_rec_lc_qualifier: forall (v: value) (ϕ: qualifier) (k: nat),
    lc_qualifier ϕ -> {k ~q> v} ϕ = ϕ.
Proof.
  destruct 1. simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  rewrite Vector.Forall_forall in H.
  eauto using open_rec_lc_value.
Qed.

Lemma open_qualifier_idemp: forall u (v: value) (ϕ: qualifier) (k: nat),
    lc v ->
    {k ~q> u} ({k ~q> v} ϕ) = ({k ~q> v} ϕ).
Proof.
  destruct ϕ; intros. simpl.
  f_equal.
  rewrite Vector.map_map.
  apply Vector.map_ext_in.
  eauto using open_value_idemp.
Qed.

Lemma open_am_idemp: forall u (v: value) (a: am) (k: nat),
    lc v ->
    {k ~a> u} ({k ~a> v} a) = ({k ~a> v} a).
Proof.
  induction a; intros; simpl; f_equal; eauto using open_qualifier_idemp.
Qed.

Lemma open_pty_idemp: forall u (v: value) (ρ: pty) (k: nat),
    lc v ->
    {k ~p> u} ({k ~p> v} ρ) = {k ~p> v} ρ
with open_hty_idemp: forall u (v: value)  (τ: hty) (k: nat),
    lc v ->
    {k ~h> u} ({k ~h> v} τ) = {k ~h> v} τ.
Proof.
  destruct ρ; intros; simpl; f_equal; eauto using open_qualifier_idemp.
  destruct τ; intros; simpl; f_equal; eauto using open_am_idemp.
Qed.

Lemma subst_intro_qualifier: forall (ϕ: qualifier) (x:atom) (w: value) (k: nat),
    x # ϕ ->
    lc w -> {x := w}q ({k ~q> x} ϕ) = ({k ~q> w} ϕ).
Proof.
  intros.
  specialize (subst_open_qualifier ϕ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_qualifier; auto.
Qed.

Lemma open_lc_qualifier: forall (u: value) (ϕ: qualifier),
    (* don't body defining body yet. *)
    (exists L : aset, forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) ->
    lc u ->
    lc_qualifier ({0 ~q> u} ϕ).
Proof.
  intros. destruct H.
  let acc := collect_stales tt in pose acc.
  pose (Atom.fv_of_set a).
  assert (a0 ∉ a). apply Atom.fv_of_set_fresh.
  erewrite <- subst_intro_qualifier; auto. instantiate (1:= a0).
  apply subst_lc_qualifier; auto. apply H.
  my_set_solver. my_set_solver.
Qed.

Lemma open_swap_qualifier: forall (ϕ: qualifier) i j (u v: value),
    lc u ->
    lc v ->
    i <> j ->
    {i ~q> v} ({j ~q> u} ϕ) = {j ~q> u} ({i ~q> v} ϕ).
Proof.
  destruct ϕ. intros. simpl.
  f_equal. rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using open_swap_value.
Qed.

Lemma open_lc_respect_qualifier: forall (ϕ: qualifier) (u v : value) k,
    lc_qualifier ({k ~q> u} ϕ) ->
    lc u ->
    lc v ->
    lc_qualifier ({k ~q> v} ϕ).
Proof.
  intros. sinvert H.
  destruct ϕ. simpl in *. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map in *.
  rewrite Forall_map in *.
  eapply Forall_impl; eauto.
  simpl. eauto using open_lc_respect_value.
Qed.

Lemma closed_pty_subseteq_proper s1 s2 ρ :
  closed_pty s1 ρ ->
  s1 ⊆ s2 ->
  closed_pty s2 ρ.
Proof.
  intros. sinvert H. split. eauto.
  my_set_solver.
Qed.
