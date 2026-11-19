import AFTD.Prelude
import AFTD.Kb.Optimization.SubmodularRandomSampleGuarantee
import AFTD.Kb.Optimization.SubmodularUniversalFamily
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submodular_random_sample_guarantee_iff_universal_family

Topic: submodular   Node: a809f2f9f9b3

Provenance: helper lemma. arXiv:2611.23637 Sec. 1.1

A sample of t subsets achieves the gamma-approximation guarantee for submodular maximization if and only if the image of the sample is a gamma-universal family.
-/

/-- A sample of t subsets achieves the gamma-approximation guarantee if and only if its image is a gamma-universal family. -/
theorem submodular_random_sample_guarantee_iff_universal_family {n t : ℕ}
    (R : Fin t → Finset (Fin n)) (γ : ℝ) :
    submodular_random_sample_guarantee R γ ↔
      submodular_universal_family (Finset.image R Finset.univ) γ := by
  unfold submodular_random_sample_guarantee submodular_universal_family
  constructor
  · intro h f hf_nonneg hf_submod
    rcases h f hf_nonneg hf_submod with ⟨i, hi⟩
    refine ⟨R i, ?_, hi⟩
    exact Finset.mem_image_of_mem R (Finset.mem_univ i)
  · intro h f hf_nonneg hf_submod
    rcases h f hf_nonneg hf_submod with ⟨R', hR', hR'prop⟩
    rw [Finset.mem_image] at hR'
    rcases hR' with ⟨i, -, rfl⟩
    exact ⟨i, hR'prop⟩
