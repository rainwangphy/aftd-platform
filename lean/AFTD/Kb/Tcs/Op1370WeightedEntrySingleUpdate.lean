import AFTD.Prelude

/-!
# op1370_weighted_entry_single_update

Topic: combinatorics   Node: 4a4704d422a4

Provenance: helper lemma.

Changing one set weight changes the weighted incidence entry by the corresponding rank-one term.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_weighted_entry_single_update
    {α K : Type*} [DecidableEq α] [Fintype α] [Field K]
    (q : Finset α → K) (Y : Finset α) (t : K) (A B : Finset α) :
    (∑ X : Finset α, (q X + if X = Y then t else 0) *
      ((if A ⊆ X then (-1 : K) ^ (X \ A).card else 0) * (if X ⊆ B then 1 else 0))) =
    (∑ X : Finset α, q X *
      ((if A ⊆ X then (-1 : K) ^ (X \ A).card else 0) * (if X ⊆ B then 1 else 0))) +
      t * ((if A ⊆ Y then (-1 : K) ^ (Y \ A).card else 0) * (if Y ⊆ B then 1 else 0)) := by
  classical
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  rw [Finset.sum_eq_single Y]
  · simp
  · intro X _ hX
    simp [hX]
  · intro h
    exact (h (Finset.mem_univ Y)).elim
