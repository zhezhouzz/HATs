From stdpp Require Import stringmap mapset.

(** We use the string as variables in the core langauge *)
Definition atom := string.
Definition amap := stringmap.
Definition aset := stringset.

(** The Stale will gather all free variables in type context, values, terms... *)
Class Stale {D} A := stale : A -> D.

Definition fv_of_set (s: aset): atom := fresh_string_of_set "x" s.
Lemma fv_of_set_fresh (s: aset) : (fv_of_set s) ∉ s.
Proof.
  apply fresh_string_of_set_fresh.
Qed.

Definition atom_dec: ∀ s1 s2 : atom, {s1 = s2} + {s1 ≠ s2} := string_dec.
Definition atom_eqb: atom → atom → bool := String.eqb.
Definition atom_eqb_spec (s1 s2 : atom): reflect (s1 = s2) (atom_eqb s1 s2) := String.eqb_spec s1 s2.
