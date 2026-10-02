import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.GameTheoryEconomics.SubmodUnionMarginalLe

/-!
# submod_biUnion_le_sum

Topic: fair_division   Node: d874b244a12e

A monotone submodular set function with v(empty) = 0 is subadditive over a finite family of sets.
-/

/-- A monotone submodular set function with `v ∅ = 0` is subadditive over a family of sets. -/
theorem submod_biUnion_le_sum {m n : ℕ} (v : Finset (Fin m) → ℝ) (hmono : Monotone v)
    (hsub : is_submodular v) (h0 : v ∅ = 0) (K : Finset (Fin n)) (B : Fin n → Finset (Fin m)) :
    v (K.biUnion B) ≤ ∑ j ∈ K, v (B j) := by
  induction K using Finset.induction_on with
  | empty => simp [h0]
  | insert a K ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := submod_union_marginal_le v hmono hsub (Finset.empty_subset (B a)) (K.biUnion B)
    rw [Finset.empty_union, h0] at h
    linarith
