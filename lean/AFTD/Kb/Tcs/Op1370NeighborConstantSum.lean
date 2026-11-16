import AFTD.Prelude

/-!
# op1370_neighbor_constant_sum

Topic: combinatorics   Node: 5a2131970e81

Provenance: helper lemma.

A sum over a point and its disjoint neighborhood is one plus the neighborhood size times the constant.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_neighbor_constant_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι) (x : ι)
    (hx : x ∉ N) (c : ℚ) :
    (∑ a, (if a = x then 1 else if a ∈ N then c else 0)) =
      1 + (N.card : ℚ) * c := by
  have heq (a : ι) : (if a = x then 1 else if a ∈ N then c else 0) =
      (if a = x then 1 else 0) + (if a ∈ N then c else 0) := by
    by_cases h : a = x
    · subst a
      simp [hx]
    · simp [h]
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  have hs : (∑ a, if a = x then (1 : ℚ) else 0) = 1 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro a _ ha
      simp [ha]
    · intro h
      exact (h (Finset.mem_univ x)).elim
  have hn : (∑ a, if a ∈ N then c else 0) = (N.card : ℚ) * c := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp only [Finset.sum_const]
    exact nsmul_eq_mul _ _
  rw [hs, hn]
