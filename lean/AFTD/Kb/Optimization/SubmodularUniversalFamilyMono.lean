import AFTD.Prelude
import AFTD.Kb.Optimization.SubmodularUniversalFamily
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submodular_universal_family_mono

Topic: submodular   Node: cfe6d8a75c63

Provenance: helper lemma. arXiv:2611.23637 Sec. 1.1

If a family of subsets is a gamma-universal family for non-negative submodular maximization, then any superset family is also a gamma-universal family.
-/

/-- Universal families are monotone under taking supersets. -/
theorem submodular_universal_family_mono {n : ℕ} {F F' : Finset (Finset (Fin n))} {γ : ℝ}
    (hsub : F ⊆ F') (hF : submodular_universal_family F γ) :
    submodular_universal_family F' γ := by
  intro f hf_nonneg hf_submod
  obtain ⟨R, hRF, hR⟩ := hF f hf_nonneg hf_submod
  exact ⟨R, hsub hRF, hR⟩
