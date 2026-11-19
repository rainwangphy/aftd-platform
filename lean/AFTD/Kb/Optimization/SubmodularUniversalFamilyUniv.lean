import AFTD.Prelude
import AFTD.Kb.Optimization.SubmodularUniversalFamily
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submodular_universal_family_univ

Topic: submodular   Node: c233c7aec024

Provenance: helper lemma. arXiv:2611.23637 Sec. 1.1

The family of all subsets of {0, ..., n-1} is a 1-universal family for non-negative submodular maximization.
-/

/-- The universal family of all subsets achieves factor 1 for every non-negative submodular function. -/
theorem submodular_universal_family_univ (n : ℕ) :
    submodular_universal_family (Finset.univ : Finset (Finset (Fin n))) 1 := by
  intro f _ _
  have hne : (Finset.univ : Finset (Finset (Fin n))).Nonempty := ⟨∅, Finset.mem_univ _⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.univ.exists_max_image f hne
  refine ⟨R, hRmem, fun S => ?_⟩
  rw [one_mul]
  exact hRmax S (Finset.mem_univ S)
