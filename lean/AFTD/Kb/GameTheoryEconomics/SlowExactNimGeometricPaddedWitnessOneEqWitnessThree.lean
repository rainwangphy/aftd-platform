import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGeometricPaddedWitness
import AFTD.Kb.GameTheoryEconomics.SlowExactNimWitnessThree

/-!
# slow_exact_nim_geometric_padded_witness_one_eq_witness_three

Topic: combinatorial_games   Node: fd87f5eb6ef5

Provenance: helper lemma. arXiv:2611.14546; OP-1728

For every natural number k, the geometric padded witness position slow_exact_nim_geometric_padded_witness 1 k on k + 1 piles is equal to slow_exact_nim_witness_three k.
-/

/-- For excess r = 1, the geometric padded witness coincides with slow_exact_nim_witness_three. -/
theorem slow_exact_nim_geometric_padded_witness_one_eq_witness_three (k : ℕ) :
    slow_exact_nim_geometric_padded_witness 1 k = slow_exact_nim_witness_three k := by
  funext ⟨i, _⟩
  unfold slow_exact_nim_geometric_padded_witness slow_exact_nim_witness_three
  rcases i with _ | (_ | i) <;> rfl
