import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# is_submodular_add

Topic: submodular   Node: 1770fe3cb355

Provenance: helper lemma. step towards matroid_symmetry_gap_integral_lt_eight_seventeenths

The pointwise sum of two submodular set functions is submodular.
-/

/-- The pointwise sum of two submodular set functions is submodular. -/
theorem is_submodular_add {m : ℕ} (f g : Finset (Fin m) → ℝ) (hf : is_submodular f) (hg : is_submodular g) : is_submodular (f + g) := by
  intro S T j hST hj
  have h1 := hf S T j hST hj
  have h2 := hg S T j hST hj
  simp only [Pi.add_apply]
  linarith
