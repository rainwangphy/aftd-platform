import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamFamily

/-!
# restricted_cycle_one_param_family_subset_excluded_family

Topic: elementary_number_theory   Node: 20c67bdf6832

Provenance: helper lemma. arXiv:2610.40342 Theorem 5.1

For any natural numbers r and n, the one-parameter family restricted_cycle_one_param_family r n is a subset of restricted_cycle_excluded_family r n.
-/

/-- The one-parameter family of excluded sets is a subset of the family of all excluded sets containing {1, ..., r}. -/
theorem restricted_cycle_one_param_family_subset_excluded_family (r n : ℕ) :
    restricted_cycle_one_param_family r n ⊆ restricted_cycle_excluded_family r n := by
  intro s hs
  rw [restricted_cycle_one_param_family, Finset.mem_insert] at hs
  rw [restricted_cycle_excluded_family, Finset.mem_image]
  rcases hs with rfl | hs
  · refine ⟨∅, ?_, ?_⟩
    · simp
    · simp
  · rcases Finset.mem_image.mp hs with ⟨k, hk, rfl⟩
    refine ⟨{k}, ?_, rfl⟩
    rw [Finset.mem_powerset, Finset.singleton_subset_iff]
    exact hk
