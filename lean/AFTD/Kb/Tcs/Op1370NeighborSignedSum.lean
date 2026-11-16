import AFTD.Prelude

/-!
# op1370_neighbor_signed_sum

Topic: combinatorics   Node: e4c4e01d1ef9

Provenance: helper lemma.

The signed sum over a point and its disjoint neighborhood is determined by the common neighbor sign.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_neighbor_signed_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι) (x : ι)
    (hx : x ∉ N) (σ : ι → ℚ) (c : ℚ)
    (hs : ∀ a ∈ N, σ a = c * σ x) :
    (∑ a, (if a = x then σ a else if a ∈ N then σ a else 0)) =
      σ x + (N.card : ℚ) * (c * σ x) := by
  have heq (a : ι) : (if a = x then σ a else if a ∈ N then σ a else 0) =
      (if a = x then σ a else 0) + (if a ∈ N then σ a else 0) := by
    by_cases h : a = x
    · subst a
      simp [hx]
    · simp [h]
  simp_rw [heq]
  simp only [Finset.sum_add_distrib]
  have hn : (∑ a, if a ∈ N then σ a else 0) = (N.card : ℚ) * (c * σ x) := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_congr rfl hs]
    simp only [Finset.sum_const]
    exact nsmul_eq_mul _ _
  rw [hn]
  have hs : (∑ a, if a = x then σ a else 0) = σ x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro a _ ha
      simp [ha]
    · intro h
      exact (h (Finset.mem_univ x)).elim
  rw [hs]
