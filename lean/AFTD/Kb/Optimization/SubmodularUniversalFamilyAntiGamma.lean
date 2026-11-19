import AFTD.Prelude
import AFTD.Kb.Optimization.SubmodularUniversalFamily
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submodular_universal_family_anti_gamma

Topic: submodular   Node: dba09b5df69a

Provenance: helper lemma. arXiv:2611.23637 Sec. 1.1

If a family of subsets is a gamma-universal family for non-negative submodular maximization and gamma' <= gamma, then it is also a gamma'-universal family.
-/

/-- Universal families are monotone with respect to the approximation factor. -/
theorem submodular_universal_family_anti_gamma {n : ℕ} {F : Finset (Finset (Fin n))} {γ γ' : ℝ}
    (hγ : γ' ≤ γ) (hF : submodular_universal_family F γ) :
    submodular_universal_family F γ' := by
  intro f hf_nonneg hf_submod
  obtain ⟨R, hR_in, hR⟩ := hF f hf_nonneg hf_submod
  exact ⟨R, hR_in, fun S => (mul_le_mul_of_nonneg_right hγ (hf_nonneg S)).trans (hR S)⟩
