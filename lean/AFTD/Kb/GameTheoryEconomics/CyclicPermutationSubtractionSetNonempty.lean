import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicPermutationSubtractionSet
import AFTD.Kb.Tcs.MultidimInstanceExists

/-!
# cyclic_permutation_subtraction_set_nonempty

Topic: combinatorial_games   Node: d5b62a7e1f0c

Provenance: helper lemma. arXiv:2611.09157

For any natural numbers d, s, a, b, the finite set cyclic_permutation_subtraction_set d s a b is nonempty.
-/

/-- The cyclic permutation subtraction set is always nonempty. -/
theorem cyclic_permutation_subtraction_set_nonempty (d s a b : ℕ) :
    (cyclic_permutation_subtraction_set d s a b).Nonempty := by first | exact multidim_instance_exists | (apply multidim_instance_exists <;> assumption) | (apply multidim_instance_exists <;> simp_all) | simpa using multidim_instance_exists | (simp only [cyclic_permutation_subtraction_set] at *; first | exact multidim_instance_exists | (apply multidim_instance_exists <;> assumption) | (apply multidim_instance_exists <;> simp_all) | simpa using multidim_instance_exists)
