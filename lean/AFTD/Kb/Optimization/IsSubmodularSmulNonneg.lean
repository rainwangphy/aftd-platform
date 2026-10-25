import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# is_submodular_smul_nonneg

Topic: submodular   Node: 8aedb3a7f543

Provenance: helper lemma. step towards matroid_symmetry_gap_integral_lt_eight_seventeenths

Non-negative scaling preserves submodularity of a set function.
-/

/-- Non-negative scaling preserves submodularity of a set function. -/
theorem is_submodular_smul_nonneg {m : ℕ} (c : ℝ) (hc : 0 ≤ c) (f : Finset (Fin m) → ℝ) (hf : is_submodular f) : is_submodular (c • f) := by
  intro S T j hST hj
  have h1 := hf S T j hST hj
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith
