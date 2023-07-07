From CT Require Import Atom.
From stdpp Require Export prelude fin_maps fin_map_dom.
From Hammer Require Export Tactics.

Import Atom.

(** * Some tactics in the file is inspired by OADT: https://github.com/ccyip/oadt *)
(** * Fold over hypotheses *)

Ltac revert_all :=
  repeat match goal with
         | H : _ |- _ => revert H
         end.

(** This cool trick to fold over hypotheses is inspired by
https://sympa.inria.fr/sympa/arc/coq-club/2014-12/msg00034.html *)
Ltac get_hyps :=
  constr:(ltac:(revert_all; constructor) : True).

(** Run [tac] on each hypothesis. *)
Tactic Notation "do_hyps" tactic3(tac) :=
  let hs := get_hyps in
  let rec go hs :=
      lazymatch hs with
      | ?hs ?H => tac H; go hs
      | _ => idtac
      end in
  go hs.

(** Run [tac] on each hypothesis matching [pat]. *)
Tactic Notation "select" "!" open_constr(pat) tactic3(tac) :=
  let T := lazymatch goal with
           | H : pat |- _ => type of H
           end in
  do_hyps (fun H => lazymatch type of H with
                  | pat => tac H
                  | _ => idtac
                  end);
  (* Clear the shelved. *)
  unify T pat.

(** Fold over hypotheses and return the [constr] result. Run [tac] on each
hypothesis with the accumulator. [acc] is the initial accumulator. *)
Ltac fold_hyps acc tac :=
  let hs := get_hyps in
  let rec go hs acc :=
      lazymatch hs with
      | ?hs ?H => let acc' := tac H acc in go hs acc'
      | _ => acc
      end in
  go hs acc.

(** Fold over hypotheses with continuation. [acc] and [tac] are the same as in
[fold_hyps_nok]. [ktac] is the continuation run on the final result. *)
Tactic Notation "fold_hyps_cont" constr(acc) tactic3(tac) tactic3(ktac) :=
  let x := fold_hyps acc tac in
  ktac x.

(** * General purpose tactics  *)

(** Check [a] contains [pat]. *)
Tactic Notation "contains" constr(a) open_constr(pat) :=
  lazymatch a with
  | context g [pat] => let a' := context g [pat] in
                       unify a a'
  end.

(** Check goal matches pattern [pat]. *)
Tactic Notation "goal_is" open_constr(pat) :=
  lazymatch goal with
  | |- pat => lazymatch goal with
              | |- ?T => unify T pat
              end
  end.

(** Check goal contains [pat]. *)
Tactic Notation "goal_contains" open_constr(pat) :=
  lazymatch goal with
  | |- ?T => contains T pat
  end.

Ltac higher_order_reflexivity :=
  match goal with
  | |- (?f ?a) = ?b =>
    match eval pattern a in b with
    | ?f' _ => unify f f'; reflexivity
    end
  end.

(** Substitute [s] for subterm [t] in term [T]. *)
Ltac subst_pattern T t s :=
  match eval pattern t in T with
  | ?f _ => let T' := eval cbv beta in (f s) in T'
  end.

(** ** Set solving *)

(** Much faster set solving tactic, with less solving strength. *)
Tactic Notation "fast_set_solver" :=
  solve [try fast_done; repeat (set_unfold; subst; intuition)].

(** Faster set solving tactic. Stronger than [fast_set_solver], but also
slower. *)
Tactic Notation "fast_set_solver" "*" :=
  try fast_done; set_unfold; set_unfold; firstorder; auto.

Ltac set_fold_not :=
  change (?x ∈ ?v -> False) with (x ∉ v) in *;
  change (?x = ?v -> False) with (x <> v) in *.

(** Pruning the hypotheses before set solving can _dramatically_ improve
performance. The following pruning tactics are based on heuristics, and they can
make the goal unprovable. While they are unsound, they still work fine in our
cases. A better approach is probably similar to finding a transitive closure of
hypotheses against some "potentially needed" criteria. *)

(** This pruning tactic is conservative, hence the name "safe". However, it can
still make the goal unprovable. For example, it does not consider, say, that the
set relations may appear in a conjunction. *)
(* TODO: is there a way to check if the conclusion of a hypothesis has certain
"head"? I am using [context [_ -> _]] for now, which has some false
negatives. *)
Ltac set_prune_hyps_safe :=
  simpl;
  set_fold_not;
  repeat
    match goal with
    | H : ?T |- _ =>
      lazymatch T with
      | _ ⊆ _ => fail
      | _ ≡ ∅ => rewrite H in *; clear H
      | _ ≡ _ => fail
      | _ ∈ _ => fail
      | _ ∉ _ => fail
      | _ <> _ => fail
      | context [_ -> _ ⊆ _] => fail
      | context [_ -> _ ≡ _] => fail
      | context [_ -> _ ∈ _] => fail
      | context [_ -> _ ∉ _] => fail
      | context [_ -> _ <> _] => fail
      | _ => clear H
      end
    end;
  repeat
    match goal with
    | H : _ ∉ {[_]} |- _ => apply not_elem_of_singleton_1 in H
    end;
  (* Clear a subset relation if it is subsumed by another hypothesis. This
  simple heuristic can result in ~50x faster set solving in some cases. *)
  repeat
    match goal with
    | H : ?S ⊆ ?U, H' : ?S ⊆ ?V |- _ =>
      let rec go U :=
          lazymatch U with
          | ?U1 ∪ ?U2 => go U1; go U2
          | _ =>
            lazymatch V with
            | context [U] => idtac
            end
          end in go U; clear H'
    end.

(** [set_hyp_filter] filters a hypothesis in continuation style, so we can
thread a few filters. *)
Tactic Notation "set_hyp_filter" constr(T) ">>=" tactic3(tac) :=
  lazymatch T with
  | _ ⊆ _ => fail
  | _ ≡ _ => fail
  | context [_ -> _ ⊆ _] => fail
  | context [_ -> _ ≡ _] => fail
  | _ => tac T
  end.

Tactic Notation "set_hyp_filter" constr(T) constr(x) ">>=" tactic3(tac) :=
  lazymatch T with
  | context [x] =>
    lazymatch T with
    | _ ∈ _ => fail
    | _ ∉ _ => fail
    | _ <> _ => fail
    | context [_ -> _ ∈ _] => fail
    | context [_ -> _ ∉ _] => fail
    | context [_ -> _ <> _] => fail
    | _ => tac T
    end
  | _ => tac T
  end.

(** This pruning tactic is more radical. It is more likely to destroy the
goal, but it also offers better performance in certain cases. *)
Ltac set_prune_hyps :=
  set_prune_hyps_safe;
  try
    lazymatch goal with
    | |- _ ⊆ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun _ => clear H)
        end
    | |- ?y ∉ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T y >>= (fun _ => clear H))
        end
    | |- ?x <> ?y =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T x >>= (fun T =>
              set_hyp_filter T y >>= (fun _ => clear H)))
        end
    end.

Tactic Notation "set_solver" "!" :=
  set_prune_hyps_safe; set_solver.
Tactic Notation "set_solver" "!!" :=
  set_prune_hyps; set_solver.

Tactic Notation "fast_set_solver" "!" :=
  set_prune_hyps_safe; fast_set_solver.
Tactic Notation "fast_set_solver" "!!" :=
  set_prune_hyps; fast_set_solver.

Tactic Notation "fast_set_solver" "*" "!" :=
  set_prune_hyps_safe; fast_set_solver*.
Tactic Notation "fast_set_solver" "*" "!!" :=
  set_prune_hyps; fast_set_solver*.

(** ** Forward reasoning *)

(** Duplicate hypothesis [H] and continue with [tac]. *)
Tactic Notation "dup_hyp" hyp(H) tactic3(tac) :=
  let H' := fresh "H" in
  pose proof H as H'; tac H'.

(** Check if [p] is not in the hypothesis context. *)
Ltac no_hyp p :=
  match type of p with
  | ?T =>
    lazymatch goal with
    | H : T |- _ => fail "hypothesis exists"
    | _ => idtac
    end
  end.

(** Add hypothesis [p] if it is not in the context already. *)
Ltac add_hyp p := no_hyp p; pose proof p.

(** Check if there is another hypothesis that is the same as [H]. *)
Ltac exists_same_hyp H :=
  match type of H with
  | ?X =>
    match goal with
    | H' : X |- _ =>
      lazymatch H with
      | H' => fail
      | _ => idtac
      end
    end
  end.

(** Check if [H] is unique in the context. *)
Ltac uniq_hyp H :=
  tryif exists_same_hyp H then fail "hypothesis is not unique" else idtac.

(** Blocking and unblocking hypotheses. They are used as markers. *)
Ltac block_hyp H :=
  match type of H with
  | ?T => change (block T) in H
  end.
Ltac unblock_hyp H := unfold block in H.
Ltac unblock_hyps := unfold block in *.
Ltac clear_blocked := try select! (block _) (fun H => clear H).
Ltac not_blocked_hyp H :=
  lazymatch type of H with
  | block _ => fail
  | _ => idtac
  end.

(** [dup_hyp!] tactics allow we to implement forward reasoning tactics a la
saturation. Currently, our saturation is naive, ad-hoc and quite fragile. It
also requires a few boilerplates. *)
(** Duplicate [H] and continue with [tac]. We check if [tac] produces something
that is already in the context, and fail in this case to avoid divergence. This
tactic also continues with [ktac] after checking, in case [ktac] destroys the
hypothesis completely, e.g., by [destruct]. We use blocking to mark a hypothesis
has been produced before, and we need to clear the blocked hypotheses after
saturation. It would be better if we can create and access another global
context in ltac, so we can thread a few tactics together without messing with
the hypothesis context. *)
Tactic Notation "dup_hyp" "!" hyp(H) tactic3(tac) "with" tactic3(ktac) :=
  dup_hyp H (fun H => tac H;
                    dup_hyp H (fun H => block_hyp H; uniq_hyp H);
                    ktac H).

Tactic Notation "dup_hyp" "!" hyp(H) tactic3(tac) :=
  dup_hyp! H tac with (fun _ => idtac).

(** ** Hypothesis application *)

Ltac curry_tac f p :=
  let rec go p :=
      lazymatch p with
      | (?a, ?p) =>
        curry_tac (f a) p
      | tt => f
      end in go p.

(** [apply_eq] applies hypothesis [H], and generates equality subgoals for the
arguments if the arguments can not be unified. Note that this tactic only
generates equality subgoals from the last argument to the first argument that
can not be substituted, most likely due to dependent type. *)
Tactic Notation "apply_eq" uconstr(H) "by" tactic3(tac) :=
  let rec go R p :=
      match R with
      | ?R ?a =>
          let e := fresh "e" in
          let f := constr:(fun e =>
                             ltac:(let g := curry_tac (R e) p in
                                   exact g)) in
          let T := type of a in
          let a := mk_evar T in
          refine (eq_ind a f _ _ _); [ go R constr:((a, p)) | ]
      | _ => idtac
      end in
    match goal with
    | |- ?T => go T constr:(tt)
    end; [ tac H | .. ]; try reflexivity.

Tactic Notation "apply_eq" uconstr(H) := apply_eq H by (fun H => apply H).
Tactic Notation "eapply_eq" uconstr(H) := apply_eq H by (fun H => eapply H).

(** [auto_apply] applies the first appliable hypothesis of the same shape. It is
useful for applying induction hypotheses automatically. *)
Tactic Notation "auto_apply" "by" tactic3(tac) :=
  try eassumption;
  match goal with
  | H : context [_ -> ?C] |- ?C => tac H
  | H : context [_ -> ?C _] |- ?C _ => tac H
  | H : context [_ -> ?C _ _] |- ?C _ _ => tac H
  | H : context [_ -> ?C _ _ _] |- ?C _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _] |- ?C _ _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _ _] |- ?C _ _ _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _ _ _] |- ?C _ _ _ _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _ _ _ _] |- ?C _ _ _ _ _ _ _ => tac H
  end.

Tactic Notation "auto_apply" := auto_apply by (fun H => apply H).
Tactic Notation "auto_eapply" := auto_apply by (fun H => eapply H).
Tactic Notation "auto_apply_eq" := auto_apply by (fun H => apply_eq H).
Tactic Notation "auto_eapply_eq" := auto_apply by (fun H => eapply_eq H).

(** ** General solvers *)

Tactic Notation "equiv_naive_solver" "by" tactic3(tac) :=
  solve [ reflexivity
        | tac
        | symmetry; tac
        | etrans; solve [tac | symmetry; tac] ].

Ltac equiv_naive_solver :=
  equiv_naive_solver by eauto.

#[export]
Hint Extern 1 (_ ≡ _) => equiv_naive_solver : equiv_naive_solver.
