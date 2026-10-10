import AFTD.Prelude

/-!
# sum_over_snoc

Topic: classical_mechanics   Node: 6a85a51755ed

Provenance: formalization of a published result. Source: Physlib, `sum_over_snoc`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Contraction.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Split a sum over `(k+1)`-tuples into the last entry and the initial `k`-tuple.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Matrix in
variable {α : Type} [DecidableEq α] [Fintype α] in
/-- Split a sum over `(k+1)`-tuples into the last entry and the initial `k`-tuple. -/
lemma sum_over_snoc {X : Type*} [Fintype X] {M : Type*} [AddCommMonoid M] {k : ℕ}
    (F : (Fin (k + 1) → X) → M) :
    ∑ h : Fin (k + 1) → X, F h = ∑ h' : Fin k → X, ∑ c : X, F (Fin.snoc h' c) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ => X)) F, Fintype.sum_prod_type, Finset.sum_comm]
  rfl
