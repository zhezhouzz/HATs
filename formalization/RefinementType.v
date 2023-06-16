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
| aemp
| aϵ
| aevent (op: effop) (ϕ: qualifier) (** bvar 1 is argument, bvar 0 is result value *)
| aconcat (a: am) (b: am)
| aunion (a: am) (b: am)
| acomp (a: am)
| astar (a: am)
.

Notation "'⟨' op '|' ϕ '⟩'" := (aevent op ϕ) (at level 5, format "⟨ op | ϕ ⟩", op constr, ϕ constr).
Notation " a ';+' b " := (aconcat a b) (at level 5, format "a ;+ b", b constr, a constr, right associativity).

Definition aany: am.
Admitted.

Notation "∘" := aany (at level 5).
Notation "a∅" := aemp (at level 80, right associativity).

Inductive pty : Type :=
| basepty (B: base_ty) (ϕ: qualifier)
| arrpty (ρ: pty) (T: ty) (pre: am) (post: list (am * pty)).

Lemma pty_ind'
  (P : pty → Prop)
  (f0 : ∀ (B : base_ty) (ϕ : qualifier), P (basepty B ϕ))
  (f1 : ∀ ρ : pty,
      P ρ →
      ∀ (T : ty) (pre : am) (post : list (am * pty)),
        Forall (fun '(_, ρ') => P ρ') post ->
        P (arrpty ρ T pre post))
  : forall (p : pty), P p.
Proof.
  fix F 1. intros.
  refine (
    match p return (P p) with
    | basepty B ϕ => f0 B ϕ
    | arrpty ρ T pre post => _
    end).
  apply f1; eauto.
  induction post; intuition.
Defined.

Definition postam: Type := list (am * pty).

(* Print pty_ind. *)

Inductive hty : Type :=
| hty_ (T: ty) (pre: am) (post: list (am * pty)).

Global Hint Constructors hty: core.
Global Hint Constructors pty: core.
Global Hint Constructors am: core.

Notation "'{v:' B '|' ϕ '}'" := (basepty B ϕ) (at level 5, format "{v: B | ϕ }", B constr, ϕ constr).
Notation "'[:' T '|' a '⇒' b ']'" := (hty_ T a b) (at level 5, format "[: T | a ⇒ b ]", T constr, a constr, b constr).
Notation "'-:' ρ '⤑[:' T '|' a '⇒' b ']' " :=
  (arrpty ρ T a b) (at level 80, format "-: ρ ⤑[: T | a ⇒ b ]", right associativity, ρ constr, T constr, a constr, b constr).

(** Erase *)

Fixpoint pty_erase ρ : ty :=
  match ρ with
  | {v: B | _} => B
  | (-: ρ ⤑[: T | _ ⇒ _ ]) => (pty_erase ρ) ⤍ T
  end.

Definition hty_erase ρ : ty :=
  match ρ with
  | [: T | _ ⇒ _ ] => T
  end.

Class Erase A := erase : A -> ty.
#[global]
  Instance pty_erase_ : Erase pty := pty_erase.
#[global]
  Instance hty_erase_ : Erase hty := hty_erase.

Notation " '⌊' ty '⌋' " := (erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

Definition pty_to_rty (ρ: pty) := [: ⌊ ρ ⌋ | astar ∘ ⇒ [(aϵ, ρ)] ].

(** free variables *)

Fixpoint am_fv a : aset :=
  match a with
  | aemp => ∅
  | aϵ => ∅
  | aevent _ ϕ => qualifier_fv ϕ
  | aconcat a b => (am_fv a) ∪ (am_fv b)
  | aunion a b => (am_fv a) ∪ (am_fv b)
  | astar a => am_fv a
  | acomp a => am_fv a
  end.

Definition listctx_fmap {A: Type} {B: Type} (f: A -> B) (l: listctx A) :=
  List.map (fun e => (e.1, f e.2)) l.

Fixpoint pty_fv ρ : aset :=
  match ρ with
  | {v: _ | ϕ } => qualifier_fv ϕ
  | -: ρ ⤑[: _ | a ⇒ b ] => (pty_fv ρ) ∪ (am_fv a) ∪ (⋃ (List.map (fun e => am_fv e.1 ∪ pty_fv e.2) b))
  end.

Definition postam_fv (B : (list (am * pty))) := (⋃ (List.map (fun e => am_fv e.1 ∪ pty_fv e.2) B)).

Definition hty_fv ρ : aset :=
  match ρ with
  | [: _ | a ⇒ b ] => (am_fv a) ∪ postam_fv b
  end.

#[global]
  Instance pty_stale : @Stale aset pty := pty_fv.
Arguments pty_stale /.
#[global]
  Instance am_stale : @Stale aset am := am_fv.
Arguments am_stale /.
#[global]
  Instance postam_stale : @Stale aset (list (am * pty)) := postam_fv.
Arguments postam_stale /.
#[global]
  Instance hty_stale : @Stale aset hty := hty_fv.
Arguments hty_stale /.

(* The effect operator always has 2 bound variables *)
Fixpoint am_open (k: nat) (s: value) (a : am): am :=
  match a with
  | aemp => aemp
  | aϵ => aϵ
  | aevent op ϕ => aevent op (qualifier_open (S (S k)) s ϕ)
  | aconcat a b => aconcat (am_open k s a) (am_open k s b)
  | aunion a b => aunion (am_open k s a) (am_open k s b)
  | astar a => astar (am_open k s a)
  | acomp a => acomp (am_open k s a)
  end.

Fixpoint pty_open (k: nat) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {v: B | ϕ } => {v: B | qualifier_open (S k) s ϕ }
  | -: ρ ⤑[: T | a ⇒ b ] =>
      -: pty_open k s ρ ⤑[: T | am_open (S k) s a ⇒ (List.map (fun e => (am_open (S k) s e.1, pty_open (S k) s e.2)) b) ]
  end.

Definition pam_open (k: nat) (s: value) (l: list (am * pty)) : list (am * pty) :=
  (List.map (fun e => (am_open (S k) s e.1, pty_open (S k) s e.2)) l).

Definition hty_open (k: nat) (s: value) (a : hty): hty :=
  match a with
  | [: T | a ⇒ b ] => [: T | am_open k s a ⇒ pam_open k s b ]
  end.

Notation "'{' k '~p>' s '}' e" := (pty_open k s e) (at level 20, k constr).
Notation "'{' k '~a>' s '}' e" := (am_open k s e) (at level 20, k constr).
Notation "'{' k '~pa>' s '}' e" := (pam_open k s e) (at level 20, k constr).
Notation "'{' k '~h>' s '}' e" := (hty_open k s e) (at level 20, k constr).
Notation "e '^p^' s" := (pty_open 0 s e) (at level 20).
Notation "e '^a^' s" := (am_open 0 s e) (at level 20).
Notation "e '^pa^' s" := (pam_open 0 s e) (at level 20).
Notation "e '^h^' s" := (hty_open 0 s e) (at level 20).

(* Notation " '{' x '↦' v '}' " := (state_insert_value x v) (at level 20, format "{ x ↦ v }", x constr, v constr). *)

(* Notation " '{' x ':={' d '}' v '}' " := (state_subst d x v) (at level 20, format "{ x :={ d } v }", x constr, v constr). *)

Fixpoint am_subst (k: atom) (s: value) (a : am): am :=
  match a with
  | aemp => aemp
  | aϵ => aϵ
  | aevent op ϕ => aevent op (qualifier_subst k s ϕ)
  | aconcat a b => aconcat (am_subst k s a) (am_subst k s b)
  | aunion a b => aunion (am_subst k s a) (am_subst k s b)
  | astar a => astar (am_subst k s a)
  | acomp a => acomp (am_subst k s a)
  end.

Fixpoint pty_subst (k: atom) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {v: B | ϕ } => {v: B | qualifier_subst k s ϕ }
  | -: ρ ⤑[: T | a ⇒ b ] =>
      -: pty_subst k s ρ ⤑[: T | am_subst k s a ⇒ (List.map (fun e => (am_subst k s e.1, pty_subst k s e.2)) b)]
  end.

Definition postam_subst (k: atom) (s: value) (B: list (am * pty)): list (am * pty) :=
  List.map (fun e => (am_subst k s e.1, pty_subst k s e.2)) B.


Definition hty_subst (k: atom) (s: value) (a : hty): hty :=
  match a with
  | [: T | a ⇒ B ] => [: T | am_subst k s a ⇒ (postam_subst k s B)]
  end.

Notation "'{' x ':=' s '}p'" := (pty_subst x s) (at level 20, format "{ x := s }p", x constr).
Notation "'{' x ':=' s '}a'" := (am_subst x s) (at level 20, format "{ x := s }a", x constr).
Notation "'{' x ':=' s '}pa'" := (postam_subst x s) (at level 20, format "{ x := s }pa", x constr).
Notation "'{' x ':=' s '}h'" := (hty_subst x s) (at level 20, format "{ x := s }h", x constr).

(** well formed, locally closed, closed with state *)

Definition amlist_typed (B: list (am * pty)) (T: ty) :=
  (forall Bi ρi, In (Bi, ρi) B -> ⌊ ρi ⌋ = T).

Inductive valid_pty: pty -> Prop :=
| valid_pty_base: forall B ϕ, valid_pty {v: B | ϕ }
| valid_pty_arr: forall ρ T A B,
    valid_pty ρ ->
    amlist_typed B T ->
    (forall Bi ρi, In (Bi, ρi) B -> valid_pty ρi) ->
    valid_pty (-: ρ ⤑[: T | A ⇒ B ]).

Inductive valid_hty: hty -> Prop :=
| valid_hty_: forall T A B,
    amlist_typed B T -> (forall Bi ρi, In (Bi, ρi) B -> valid_pty ρi) ->
    valid_hty [: T | A ⇒ B ].

Inductive lc_am : am -> Prop :=
| lc_aemp : lc_am aemp
| lc_aϵ : lc_am aϵ
| lc_aevent: forall op ϕ (L : aset),
    (* This is quite annoying. *)
    (forall (x y : atom), x ∉ L -> y ∉ L -> lc_qualifier (ϕ ^q^ x ^q^ y)) ->
    lc_am (aevent op ϕ)
| lc_aconcat : forall a b, lc_am a -> lc_am b -> lc_am (aconcat a b)
| lc_aunion : forall a b, lc_am a -> lc_am b -> lc_am (aunion a b)
| lc_astar: forall a, lc_am a -> lc_am (astar a)
| lc_acomp : forall a, lc_am a -> lc_am (acomp a)
.

Inductive lc_pty : pty -> Prop :=
| lc_pty_base: forall B ϕ (L : aset),
    (forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) ->
    lc_pty {v: B | ϕ }
| lc_pty_arr: forall ρ T A B (L : aset),
    lc_pty ρ ->
    (forall x : atom, x ∉ L -> lc_am (A ^a^ x)) ->
    (forall x : atom, x ∉ L -> forall Bi ρi, In (Bi, ρi) B -> lc_am (Bi ^a^ x)) ->
    (forall x : atom, x ∉ L -> forall Bi ρi, In (Bi, ρi) B -> lc_pty (ρi ^p^ x)) ->
    lc_pty (-: ρ ⤑[: T | A ⇒ B ]).

Inductive lc_hty : hty -> Prop :=
| lc_hty_ : forall T A B,
    lc_am A ->
    (forall Bi ρi, In (Bi, ρi) B -> lc_am Bi) ->
    (forall Bi ρi, In (Bi, ρi) B -> lc_pty ρi) ->
    lc_hty [: T | A ⇒ B ].

Inductive closed_pty (d : aset) (ρ: pty): Prop :=
| closed_pty_: valid_pty ρ -> lc_pty ρ -> pty_fv ρ ⊆ d -> closed_pty d ρ.

Inductive closed_am (d: aset) (a: am): Prop :=
| closed_am_: lc_am a -> am_fv a ⊆ d -> closed_am d a.

Inductive closed_hty (d: aset) (ρ: hty): Prop :=
| closed_hty_: valid_hty ρ -> lc_hty ρ -> hty_fv ρ ⊆ d -> closed_hty d ρ.

(* Type context *)

Fixpoint remove_arr_pty (Γ: listctx pty) :=
  match Γ with
  | [] => []
  | (x, {v: B | ϕ}) :: Γ => (x, {v: B | ϕ}) :: remove_arr_pty Γ
  | (x, _) :: Γ =>  Γ
  end.

(* langledot *)
Notation "'⦑' x '⦒'" := (remove_arr_pty x) (at level 5, format "⦑ x ⦒", x constr).

Inductive ok_ctx: listctx pty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx pty)(x: atom) (ρ: pty),
    ok_ctx Γ ->
    closed_pty (ctxdom ⦑ Γ ⦒) ρ ->
    x ∉ ctxdom Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Definition ctx_closed_pty (Γ: listctx pty) :=
  forall Γ1 (x: atom) (ρ: pty) Γ2, Γ = Γ1 ++ [(x, ρ)] ++ Γ2 -> closed_pty (ctxdom ⦑ Γ1 ⦒) ρ.

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

Lemma ok_ctx_regular: forall Γ, ok_ctx Γ -> ok Γ /\ ctx_closed_pty Γ.
Admitted.

Definition ctx_erase (Γ: listctx pty) :=
  ⋃ ((List.map (fun e => {[e.1 := pty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** Ty Function *)
Definition mk_eq_constant c := {v: ty_of_const c | b0:c= c }.
Definition mk_bot ty := {v: ty | mk_q_under_bot }.
Definition mk_top ty := {v: ty | mk_q_under_top }.
Definition mk_eq_var ty (x: atom) := {v: ty | b0:x= x }.

(* Dummy implementation  *)
Inductive builtin_typing_relation: effop -> pty -> Prop :=
| builtin_typing_relation_: forall op ρx A B ρ,
    builtin_typing_relation op (-: ρx ⤑[: ret_ty_of_op op | A ⇒ [(B, ρ)] ]).

Lemma subst_fresh_am: forall (a: am) (x:atom) (u: value),
    x ∉ (am_fv a) -> {x := u}a a = a.
Proof.
  intros. induction a; simpl in *; eauto; repeat f_equal;
    eauto using subst_fresh_qualifier;
    auto_apply; try my_set_solver.
Qed.

Lemma subst_fresh_pty: forall (ρ: pty) (x:atom) (u: value),
    x ∉ (pty_fv ρ) -> {x := u}p ρ = ρ.
Proof.
  intros.
  induction ρ using pty_ind';
    simpl in *; f_equal; eauto using subst_fresh_qualifier.
  auto_apply. my_set_solver.
  apply subst_fresh_am. my_set_solver.
  rewrite <- map_id.
  apply map_ext_Forall.

  (* A better proof is probably first show [x ∉ ⋃ map ... post] is equivalent to
  [Forall (fun ... => x ∉ ...) post], and then go from ther. But don't bother. *)
  induction post; eauto.
  simp_hyps. simpl in *.
  decompose_Forall_hyps.
  econstructor. simpl.
  f_equal.
  apply subst_fresh_am. my_set_solver.
  auto_apply. my_set_solver.
  auto_apply. set_solver. eauto.
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
    {x := u_x }p ({y := u_y }p ρ) = {y := u_y }p ({x := u_x }p ρ).
Proof.
  intros.
  induction ρ using pty_ind'; simpl; f_equal;
    eauto using subst_commute_qualifier, subst_commute_am.
  rewrite !map_map. simpl.
  apply map_ext_Forall.
  eapply Forall_impl; eauto. intros [] **. simpl.
  f_equal; eauto using subst_commute_am.
Qed.

Lemma subst_commute_postam : forall x u_x y u_y pa,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }pa ({y := u_y }pa pa) = {y := u_y }pa ({x := u_x }pa pa).
Proof.
  intros.
  induction pa; simpl; f_equal; eauto.
  f_equal; eauto using subst_commute_pty, subst_commute_am.
Qed.
