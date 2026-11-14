import AFTD.Prelude
import AFTD.Kb.NumberTheory.AvoidsSubsetSum
import AFTD.Kb.GameTheoryEconomics.OnePlayerExtensionSubOne

/-!
# empty_avoids_subset_sum

Topic: elementary_number_theory   Node: ea02ff3151dc

Provenance: helper lemma. arXiv:2611.17205 Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem, Section 1.1

The empty set avoids every natural number $n$.
-/

/-- The empty set avoids any target integer. -/
lemma empty_avoids_subset_sum (n : ℕ) : avoids_subset_sum ∅ n := by first | exact one_player_extension_sub_one | (apply one_player_extension_sub_one <;> assumption) | (apply one_player_extension_sub_one <;> simp_all) | simpa using one_player_extension_sub_one | (simp only [avoids_subset_sum] at *; first | exact one_player_extension_sub_one | (apply one_player_extension_sub_one <;> assumption) | (apply one_player_extension_sub_one <;> simp_all) | simpa using one_player_extension_sub_one)
