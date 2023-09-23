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
| aany
| aevent (op: effop) (ϕ: qualifier) (** bvar 1 is argument, bvar 0 is result value *)
| aconcat (a: am) (b: am)
| aunion (a: am) (b: am)
| adiff (a: am) (b : am)
| astar (a: am)
.

Notation "'⟨' op '|' ϕ '⟩'" := (aevent op ϕ) (at level 5, format "⟨ op | ϕ ⟩", op constr, ϕ constr).
Notation " a ';+' b " := (aconcat a b) (at level 5, format "a ;+ b", b constr, a constr, right associativity).
Notation " a ';||' b " := (aunion a b) (at level 5, format "a ;|| b", b constr, a constr, right associativity).
Notation " a ';∖' b " := (adiff a b) (at level 5, format "a ;∖ b", b constr, a constr, right associativity).
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

Notation "'{:' B '|' ϕ '}'" := (basepty B ϕ) (at level 5, format "{: B | ϕ }", B constr, ϕ constr).
Notation "'[:' T '|' a '▶' b ']'" := (hty_ T a b) (at level 5, format "[: T | a ▶ b ]", T constr, a constr, b constr).
Notation "'-:' ρ '⤑[:' T '|' a '▶' b ']' " :=
  (arrpty ρ T a b) (at level 80, format "-: ρ ⤑[: T | a ▶ b ]", right associativity, ρ constr, T constr, a constr, b constr).

(** Erase *)

Fixpoint pty_erase ρ : ty :=
  match ρ with
  | {: B | _} => B
  | (-: ρ ⤑[: T | _ ▶ _ ]) => (pty_erase ρ) ⤍ T
  end.

Definition hty_erase ρ : ty :=
  match ρ with
  | [: T | _ ▶ _ ] => T
  end.

Class Erase A := erase : A -> ty.
#[global]
  Instance pty_erase_ : Erase pty := pty_erase.
#[global]
  Instance hty_erase_ : Erase hty := hty_erase.

Notation " '⌊' ty '⌋' " := (erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

Definition pty_to_rty (ρ: pty) := [: ⌊ ρ ⌋ | astar ∘ ▶ [(aϵ, ρ)] ].

(** free variables *)

Fixpoint am_fv a : aset :=
  match a with
  | aemp => ∅
  | aϵ => ∅
  | aany => ∅
  | aevent _ ϕ => qualifier_fv ϕ
  | aconcat a b => (am_fv a) ∪ (am_fv b)
  | aunion a b => (am_fv a) ∪ (am_fv b)
  | astar a => am_fv a
  | adiff a b => am_fv a ∪ am_fv b
  end.

Fixpoint pty_fv ρ : aset :=
  match ρ with
  | {: _ | ϕ } => qualifier_fv ϕ
  | -: ρ ⤑[: _ | a ▶ b ] => (pty_fv ρ) ∪ (am_fv a) ∪ (⋃ (List.map (fun e => am_fv e.1 ∪ pty_fv e.2) b))
  end.

Definition postam_fv (B : (list (am * pty))) := (⋃ (List.map (fun e => am_fv e.1 ∪ pty_fv e.2) B)).

Definition hty_fv ρ : aset :=
  match ρ with
  | [: _ | a ▶ b ] => (am_fv a) ∪ postam_fv b
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
  | aany => aany
  | aevent op ϕ => aevent op (qualifier_open (S (S k)) s ϕ)
  | aconcat a b => aconcat (am_open k s a) (am_open k s b)
  | aunion a b => aunion (am_open k s a) (am_open k s b)
  | astar a => astar (am_open k s a)
  | adiff a b => adiff (am_open k s a) (am_open k s b)
  end.

Fixpoint pty_open (k: nat) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {: B | ϕ } => {: B | qualifier_open (S k) s ϕ }
  | -: ρ ⤑[: T | a ▶ b ] =>
      -: pty_open k s ρ ⤑[: T | am_open (S k) s a ▶ (List.map (fun e => (am_open (S k) s e.1, pty_open (S k) s e.2)) b) ]
  end.

Definition pam_open (k: nat) (s: value) (l: list (am * pty)) : list (am * pty) :=
  (List.map (fun e => (am_open k s e.1, pty_open k s e.2)) l).

Definition hty_open (k: nat) (s: value) (a : hty): hty :=
  match a with
  | [: T | a ▶ b ] => [: T | am_open k s a ▶ pam_open k s b ]
  end.

Notation "'{' k '~p>' s '}' e" := (pty_open k s e) (at level 20, k constr).
Notation "'{' k '~a>' s '}' e" := (am_open k s e) (at level 20, k constr).
Notation "'{' k '~pa>' s '}' e" := (pam_open k s e) (at level 20, k constr).
Notation "'{' k '~h>' s '}' e" := (hty_open k s e) (at level 20, k constr).
Notation "e '^p^' s" := (pty_open 0 s e) (at level 20).
Notation "e '^a^' s" := (am_open 0 s e) (at level 20).
Notation "e '^pa^' s" := (pam_open 0 s e) (at level 20).
Notation "e '^h^' s" := (hty_open 0 s e) (at level 20).

Fixpoint am_subst (k: atom) (s: value) (a : am): am :=
  match a with
  | aemp => aemp
  | aϵ => aϵ
  | aany => aany
  | aevent op ϕ => aevent op (qualifier_subst k s ϕ)
  | aconcat a b => aconcat (am_subst k s a) (am_subst k s b)
  | aunion a b => aunion (am_subst k s a) (am_subst k s b)
  | astar a => astar (am_subst k s a)
  | adiff a b => adiff (am_subst k s a) (am_subst k s b)
  end.

Fixpoint pty_subst (k: atom) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {: B | ϕ } => {: B | qualifier_subst k s ϕ }
  | -: ρ ⤑[: T | a ▶ b ] =>
      -: pty_subst k s ρ ⤑[: T | am_subst k s a ▶ (List.map (fun e => (am_subst k s e.1, pty_subst k s e.2)) b)]
  end.

Definition postam_subst (k: atom) (s: value) (B: list (am * pty)): list (am * pty) :=
  List.map (fun e => (am_subst k s e.1, pty_subst k s e.2)) B.


Definition hty_subst (k: atom) (s: value) (a : hty): hty :=
  match a with
  | [: T | a ▶ B ] => [: T | am_subst k s a ▶ (postam_subst k s B)]
  end.

Notation "'{' x ':=' s '}p'" := (pty_subst x s) (at level 20, format "{ x := s }p", x constr).
Notation "'{' x ':=' s '}a'" := (am_subst x s) (at level 20, format "{ x := s }a", x constr).
Notation "'{' x ':=' s '}pa'" := (postam_subst x s) (at level 20, format "{ x := s }pa", x constr).
Notation "'{' x ':=' s '}h'" := (hty_subst x s) (at level 20, format "{ x := s }h", x constr).

(** well formed, locally closed, closed with state *)

Definition amlist_typed (B: list (am * pty)) (T: ty) :=
  (forall Bi ρi, In (Bi, ρi) B -> ⌊ ρi ⌋ = T).

Inductive valid_pty: pty -> Prop :=
| valid_pty_base: forall B ϕ, valid_pty {: B | ϕ }
| valid_pty_arr: forall ρ T A B (L : aset),
    valid_pty ρ ->
    amlist_typed B T ->
    (forall x : atom, x ∉ L -> forall Bi ρi, In (Bi, ρi) B -> valid_pty (ρi ^p^ x)) ->
    valid_pty (-: ρ ⤑[: T | A ▶ B ]).

Inductive valid_hty: hty -> Prop :=
| valid_hty_: forall T A B,
    amlist_typed B T -> (forall Bi ρi, In (Bi, ρi) B -> valid_pty ρi) ->
    valid_hty [: T | A ▶ B ].

Inductive lc_am : am -> Prop :=
| lc_aemp : lc_am aemp
| lc_aϵ : lc_am aϵ
| lc_aany : lc_am aany
| lc_aevent: forall op ϕ (L : aset),
    (* This is quite annoying. *)
    (forall (x : atom), x ∉ L -> forall (y : atom), y ∉ L -> lc_qualifier ({0 ~q> y} ({1 ~q> x} ϕ))) ->
    lc_am (aevent op ϕ)
| lc_aconcat : forall a b, lc_am a -> lc_am b -> lc_am (aconcat a b)
| lc_aunion : forall a b, lc_am a -> lc_am b -> lc_am (aunion a b)
| lc_astar: forall a, lc_am a -> lc_am (astar a)
| lc_adiff : forall a b, lc_am a -> lc_am b -> lc_am (adiff a b)
.

Inductive lc_pty : pty -> Prop :=
| lc_pty_base: forall B ϕ (L : aset),
    (forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) ->
    lc_pty {: B | ϕ }
| lc_pty_arr: forall ρ T A B (L : aset),
    lc_pty ρ ->
    (forall x : atom, x ∉ L -> lc_am (A ^a^ x)) ->
    (forall x : atom, x ∉ L -> forall Bi ρi, In (Bi, ρi) B -> lc_am (Bi ^a^ x)) ->
    (forall x : atom, x ∉ L -> forall Bi ρi, In (Bi, ρi) B -> lc_pty (ρi ^p^ x)) ->
    lc_pty (-: ρ ⤑[: T | A ▶ B ]).

Inductive lc_hty : hty -> Prop :=
| lc_hty_ : forall T A B,
    lc_am A ->
    (forall Bi ρi, In (Bi, ρi) B -> lc_am Bi) ->
    (forall Bi ρi, In (Bi, ρi) B -> lc_pty ρi) ->
    lc_hty [: T | A ▶ B ].

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
  | (x, {: B | ϕ}) :: Γ => (x, {: B | ϕ}) :: remove_arr_pty Γ
  | (x, _) :: Γ => remove_arr_pty Γ
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

Definition ctx_erase (Γ: listctx pty) :=
  ⋃ ((List.map (fun e => {[e.1 := pty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** Ty Function *)
Definition mk_eq_constant c := {: ty_of_const c | b0:c= c }.
Definition mk_bot ty := {: ty | mk_q_under_bot }.
Definition mk_top ty := {: ty | mk_q_under_top }.
Definition mk_eq_var ty (x: atom) := {: ty | b0:x= x }.

Lemma pty_erase_open_eq ρ k s :
  pty_erase ρ = pty_erase ({k ~p> s} ρ).
Proof.
  induction ρ; eauto.
  cbn. f_equal. eauto.
Qed.

Lemma pty_erase_subst_eq ρ x s :
  pty_erase ρ = pty_erase ({x := s}p ρ).
Proof.
  induction ρ; eauto.
  cbn. f_equal. eauto.
Qed.

Lemma hty_erase_subst_eq τ x s :
  hty_erase τ = hty_erase ({x := s}h τ).
Proof.
  destruct τ. eauto.
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

Lemma subst_fresh_am: forall (a: am) (x:atom) (u: value),
    x # a -> {x := u}a a = a.
Proof.
  intros. induction a; simpl in *; eauto; repeat f_equal;
    eauto using subst_fresh_qualifier;
    auto_apply; try my_set_solver.
Qed.

Lemma subst_fresh_pty: forall (ρ: pty) (x:atom) (u: value),
    x # ρ -> {x := u}p ρ = ρ.
Proof.
  intros.
  induction ρ using pty_ind';
    simpl in *; f_equal; eauto using subst_fresh_qualifier.
  auto_apply. my_set_solver.
  apply subst_fresh_am. my_set_solver.
  rewrite <- map_id.
  apply map_ext_Forall.

  (* A better proof is probably first show [x ∉ ⋃ map ... post] is equivalent to
  [Forall (fun ... => x ∉ ...) post] (something like
  [union_list_subseteq_not_in]), and then go from there. But don't bother yet. *)
  induction post; eauto.
  simp_hyps. simpl in *.
  decompose_Forall_hyps.
  econstructor. simpl.
  f_equal.
  apply subst_fresh_am. my_set_solver.
  auto_apply. my_set_solver.
  auto_apply. set_solver. eauto.
Qed.

Lemma subst_fresh_postam: forall (pa: postam) (x:atom) (u: value),
    x # pa -> {x := u}pa pa = pa.
Proof.
  induction pa; eauto; intros.
  destruct a. simpl in *.
  repeat f_equal.
  apply subst_fresh_am. my_set_solver.
  apply subst_fresh_pty. my_set_solver.
  auto_apply. my_set_solver.
Qed.

Lemma subst_fresh_hty: forall (τ: hty) (x:atom) (u: value),
    x # τ -> {x := u}h τ = τ.
Proof.
  destruct τ. simpl. intros.
  f_equal.
  apply subst_fresh_am. my_set_solver.
  apply subst_fresh_postam. my_set_solver.
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

Lemma subst_commute_hty : forall x u_x y u_y e,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }h ({y := u_y }h e) = {y := u_y }h ({x := u_x }h e).
Proof.
  intros.
  destruct e. simpl.
  rewrite subst_commute_am, subst_commute_postam; eauto.
Qed.

Lemma open_fv_am' (a : am) (v : value) k :
  am_fv a ⊆ am_fv ({k ~a> v} a).
Proof.
  induction a; simpl; eauto using open_fv_qualifier';
    my_set_solver.
Qed.

Lemma open_fv_pty' (ρ : pty) (v : value) k :
  pty_fv ρ ⊆ pty_fv ({k ~p> v} ρ).
Proof.
  revert k.
  induction ρ using pty_ind'; intros; simpl; eauto using open_fv_qualifier'.
  repeat apply union_mono; eauto using open_fv_am'.
  rewrite map_map. simpl.
  apply union_list_mono.
  clear - H.
  (* Should have a [Forall] to [Forall2] lemma, or something about [Forall2] and
  [map]. *)
  induction post; simpl.
  econstructor.
  destruct a. simpl.
  econstructor.
  apply union_mono. eauto using open_fv_am'.
  sinvert H. eauto.
  apply IHpost.
  sinvert H. eauto.
Qed.

Lemma remove_arr_pty_ctx_dom_union Γ Γ' :
  ctxdom ⦑ Γ ++ Γ' ⦒ = ctxdom ⦑ Γ ⦒ ∪ ctxdom ⦑ Γ' ⦒.
Proof.
  induction Γ; intros; simpl.
  my_set_solver.
  destruct a. case_split; eauto.
  simpl. rewrite <- union_assoc_L. f_equal. eauto.
Qed.

Lemma remove_arr_pty_ctx_dom_app_commute Γ Γ' :
  ctxdom ⦑ Γ ++ Γ' ⦒ = ctxdom ⦑ Γ' ++ Γ ⦒.
Proof.
  rewrite !remove_arr_pty_ctx_dom_union.
  my_set_solver.
Qed.

Lemma remove_arr_pty_ctx_dom_singleton x v :
  ctxdom ⦑ [(x, v)] ⦒ ⊆ {[x]}.
Proof.
  simpl. case_split. simpl. my_set_solver.
  simpl. my_set_solver.
Qed.

Lemma remove_arr_pty_ctx_dom_subseteq Γ :
  ctxdom ⦑ Γ ⦒ ⊆ ctxdom Γ.
Proof.
  induction Γ; intros; simpl. my_set_solver.
  repeat case_split; simpl.
  my_set_solver.
  my_set_solver.
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

Lemma postam_open_in (pa : postam) B ρ v_x k :
  In (B, ρ) ({k ~pa> v_x} pa) ->
  exists B' ρ', In (B', ρ') pa /\ B = {k ~a> v_x} B' /\ ρ = {k ~p> v_x} ρ'.
Proof.
  induction pa; simpl; intros; qauto.
Qed.

Lemma postam_in_open (pa : postam) B ρ v_x k :
  In (B, ρ) pa ->
  In ({k ~a> v_x} B, {k ~p> v_x} ρ) ({k ~pa> v_x} pa).
Proof.
  induction pa; simpl; intros; qauto.
Qed.

Lemma postam_subst_in (pa : postam) B ρ v_x x :
  In (B, ρ) ({x := v_x}pa pa) ->
  exists B' ρ', In (B', ρ') pa /\ B = {x := v_x}a B' /\ ρ = {x := v_x}p ρ'.
Proof.
  induction pa; simpl; intros; qauto.
Qed.

Lemma postam_in_subst (pa : postam) B ρ v_x x :
  In (B, ρ) pa ->
  In ({x := v_x}a B, {x := v_x}p ρ) ({x := v_x}pa pa).
Proof.
  induction pa; simpl; intros; qauto.
Qed.

Lemma open_subst_same_pty: forall x y (ρ : pty) k,
    x # ρ ->
    {x := y }p ({k ~p> x} ρ) = {k ~p> y} ρ.
Proof.
  induction ρ using pty_ind'; cbn; intros; eauto.
  f_equal. eauto using open_subst_same_qualifier.
  f_equal. auto_apply. my_set_solver.
  apply open_subst_same_am. my_set_solver.
  rewrite map_map. apply map_ext_in.
  intros [] **.
  simpl_union H0.
  eapply not_in_union_list in Hfresh0; eauto using in_map.
  cbn in *. f_equal. apply open_subst_same_am. my_set_solver.
  eapply Forall_forall in H; eauto. apply H.
  my_set_solver.
Qed.

Lemma open_subst_same_postam: forall x y (pa : postam) k,
    x # pa ->
    {x := y }pa ({k ~pa> x} pa) = {k ~pa> y} pa.
Proof.
  induction pa; intros; eauto.
  destruct a. cbn in *.
  f_equal. f_equal. apply open_subst_same_am. my_set_solver.
  apply open_subst_same_pty. my_set_solver.
  rewrite map_map. apply map_ext_in.
  intros [] **. cbn.
  simpl_union H.
  eapply not_in_union_list in Hfresh0; eauto using in_map.
  f_equal. apply open_subst_same_am. my_set_solver.
  apply open_subst_same_pty. my_set_solver.
Qed.

Lemma open_subst_same_hty: forall x y (τ : hty) k,
    x # τ ->
    {x := y }h ({k ~h> x} τ) = {k ~h> y} τ.
Proof.
  destruct τ. cbn. intros.
  f_equal. apply open_subst_same_am. my_set_solver.
  apply open_subst_same_postam. my_set_solver.
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
    lc w -> {x := w}p ({k ~p> u} ρ) = ({k ~p> {x := w}v u} ({x := w}p ρ)).
Proof.
  induction ρ using pty_ind'; cbn; intros.
  f_equal. eauto using subst_open_qualifier.
  f_equal; eauto using subst_open_am.
  rewrite !map_map. apply map_ext_in.
  intros [] **. cbn. f_equal. eauto using subst_open_am.
  eapply Forall_forall in H; eauto.
  eauto.
Qed.

Lemma subst_open_postam: forall (pa: postam) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}pa ({k ~pa> u} pa) = ({k ~pa> {x := w}v u} ({x := w}pa pa)).
Proof.
  induction pa; cbn; intros; eauto.
  destruct a. cbn. f_equal. f_equal.
  eauto using subst_open_am. eauto using subst_open_pty.
  rewrite !map_map. apply map_ext_in.
  intros [] **. cbn. f_equal; eauto using subst_open_am, subst_open_pty.
Qed.

Lemma subst_open_hty: forall (τ: hty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}h ({k ~h> u} τ) = ({k ~h> {x := w}v u} ({x := w}h τ)).
Proof.
  intros. destruct τ.
  simpl. f_equal; eauto using subst_open_am, subst_open_postam.
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

Lemma subst_open_postam_closed:
  ∀ (pa : postam) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }pa ({k ~pa> u} pa) = {k ~pa> u} ({x := w }pa pa).
Proof.
  intros. rewrite subst_open_postam; auto.
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
    lc_pty ρ -> lc u -> lc_pty ({x := u}p ρ).
Proof.
  induction 1; intros.
  econstructor. instantiate_atom_listctx.
  - apply_eq subst_lc_qualifier; eauto.
    apply subst_open_var_qualifier; eauto; my_set_solver.
  - simpl. econstructor; eauto.
    instantiate_atom_listctx.
    rewrite <- subst_open_var_am by (eauto; my_set_solver).
    eauto using subst_lc_am.
    intros x0 **. repeat specialize_with x0.
    rewrite in_map_iff in H6. simp_hyps. simpl in *.
    rewrite <- subst_open_var_am by (eauto; my_set_solver).
    eauto using subst_lc_am.
    intros x0 **. repeat specialize_with x0.
    rewrite in_map_iff in H6. simp_hyps. simpl in *.
    rewrite <- subst_open_var_pty by (eauto; my_set_solver).
    eauto.
Qed.

Lemma subst_lc_hty : forall x (u: value) (τ: hty),
    lc_hty τ -> lc u -> lc_hty ({x := u}h τ).
Proof.
  induction 1. intros.
  econstructor. eauto using subst_lc_am.
  intros. apply postam_subst_in in H3. simp_hyps. subst. eauto using subst_lc_am.
  intros. apply postam_subst_in in H3. simp_hyps. subst. eauto using subst_lc_pty.
Qed.

Lemma fv_of_subst_qualifier:
  forall x (u : value) (ϕ: qualifier),
    qualifier_fv ({x := u }q ϕ) ⊆ (qualifier_fv ϕ ∖ {[x]}) ∪ fv_value u.
Proof.
  destruct ϕ; simpl. clear. induction vals; simpl.
  my_set_solver.
  etrans.
  apply union_mono_r.
  apply fv_of_subst_value.
  my_set_solver.
Qed.

Lemma fv_of_subst_am:
  forall x (u : value) (a: am),
    am_fv ({x := u }a a) ⊆ (am_fv a ∖ {[x]}) ∪ fv_value u.
Proof.
  induction a; simpl; eauto using fv_of_subst_qualifier; my_set_solver.
Qed.

Lemma fv_of_subst_pty:
  forall x (u : value) (ρ: pty),
    pty_fv ({x := u }p ρ) ⊆ (pty_fv ρ ∖ {[x]}) ∪ fv_value u.
Proof.
  induction ρ using pty_ind'; simpl.
  eauto using fv_of_subst_qualifier.
  rewrite map_map. simpl.
  etrans.
  repeat apply union_mono.
  eauto.
  apply fv_of_subst_am.
  instantiate (1:=⋃ map (λ e : am * pty, am_fv e.1 ∪ pty_fv e.2) post ∖ {[x]} ∪ fv_value u).
  2 : my_set_solver.
  clear - H.
  induction post; simpl. my_set_solver.
  destruct a. sinvert H. simp_hyps. simpl in *.
  etrans.
  repeat apply union_mono.
  apply fv_of_subst_am.
  eauto. eauto.
  my_set_solver.
Qed.

Lemma fv_of_subst_pty_closed:
  forall x (u : value) (ρ: pty),
    closed_value u ->
    pty_fv ({x := u }p ρ) ⊆ (pty_fv ρ ∖ {[x]}).
Proof.
  intros.
  rewrite fv_of_subst_pty.
  my_set_solver.
Qed.

Lemma fv_of_subst_postam:
  forall x (u : value) (pa: postam),
    postam_fv ({x := u }pa pa) ⊆ (postam_fv pa ∖ {[x]}) ∪ fv_value u.
Proof.
  induction pa; simpl; eauto. my_set_solver.
  destruct a. simpl in *.
  cbn.
  etrans.
  repeat apply union_mono.
  apply fv_of_subst_am.
  apply fv_of_subst_pty.
  eauto.
  my_set_solver.
Qed.

Lemma fv_of_subst_hty:
  forall x (u : value) (τ: hty),
    hty_fv ({x := u }h τ) ⊆ (hty_fv τ ∖ {[x]}) ∪ fv_value u.
Proof.
  destruct τ. simpl.
  etrans.
  apply union_mono.
  apply fv_of_subst_am.
  apply fv_of_subst_postam.
  my_set_solver.
Qed.

Lemma fv_of_subst_hty_closed:
  forall x (u : value) (τ: hty),
    closed_value u ->
    hty_fv ({x := u }h τ) ⊆ (hty_fv τ ∖ {[x]}).
Proof.
  intros.
  rewrite fv_of_subst_hty.
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
  forall e, ρ = {k ~p> e} ρ.
Proof.
  revert k.
  induction ρ using pty_ind'; simpl; intros.
  f_equal. eapply open_not_in_eq_qualifier. my_set_solver.
  f_equal. auto_apply. my_set_solver.
  apply open_not_in_eq_am with (x:=x). my_set_solver.
  (* Again, an induction here is quite ugly. *)
  induction post; simpl; intros; eauto.
  sinvert H.
  destruct a. simpl in *.
  repeat f_equal.
  apply open_not_in_eq_am with x. my_set_solver.
  auto_apply. my_set_solver.
  auto_apply; eauto. my_set_solver.
Qed.

Lemma open_not_in_eq_postam (x : atom) (pa : postam) k :
  x # {k ~pa> x} pa ->
  forall e, pa = {k ~pa> e} pa.
Proof.
  induction pa; simpl; intros; eauto.
  destruct a. simpl in *.
  repeat f_equal.
  apply open_not_in_eq_am with x. my_set_solver.
  apply open_not_in_eq_pty with x. my_set_solver.
  auto_apply. my_set_solver.
Qed.

Lemma open_not_in_eq_hty (x : atom) (τ : hty) k :
  x # {k ~h> x} τ ->
  τ = {k ~h> x} τ.
Proof.
  destruct τ. simpl. intros.
  f_equal. apply open_not_in_eq_am with x. my_set_solver.
  apply open_not_in_eq_postam with x. my_set_solver.
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
  revert dependent a.
  induction H; intros;
      match goal with
      | H : _ = {_:=_}a ?a |- _ => destruct a; simpl in *; simplify_eq
      end; eauto using lc_am.
  econstructor.
  auto_exists_L_intros. specialize_with x0. specialize_with y.
  rewrite <- !subst_open_var_qualifier in H by (eauto; my_set_solver).
  eauto using lc_subst_qualifier.
Qed.

Lemma lc_subst_pty: forall x (u: value) (ρ: pty), lc_pty ({x := u}p ρ) -> lc u -> lc_pty ρ.
Proof.
  intros.
  remember (({x:=u}p) ρ).
  revert dependent ρ.
  induction H; intros.
  - destruct ρ; simpl in *; simplify_eq.
    econstructor.
    instantiate_atom_listctx.
    rewrite <- subst_open_var_qualifier in * by (eauto; my_set_solver).
    eauto using lc_subst_qualifier.
  - destruct ρ0; simpl in *; simplify_eq.
    econstructor; eauto.
    instantiate_atom_listctx.
    rewrite <- subst_open_var_am in * by (eauto; my_set_solver).
    eauto using lc_subst_am.
    intros. repeat specialize_with x0.
    eapply postam_in_subst in H6. eapply H2 in H6.
    rewrite <- subst_open_var_am in * by (eauto; my_set_solver).
    eauto using lc_subst_am.
    intros. repeat specialize_with x0.
    eapply H4. eauto using postam_in_subst.
    rewrite <- subst_open_var_pty in * by (eauto; my_set_solver).
    eauto.
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
