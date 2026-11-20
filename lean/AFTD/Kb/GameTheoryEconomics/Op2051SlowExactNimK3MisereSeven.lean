import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimMisere
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGeometricPaddedWitness

/-!
# op_2051_slow_exact_nim_k3_misere_seven

Topic: combinatorial_games   Node: b1409fa0bc43

Provenance: helper lemma. arXiv:2611.14546; OP-2051

In slow exact 3-Nim on 5 piles, the geometric padded witness position slow_exact_nim_geometric_padded_witness 2 3 has misère invariant 7.
-/

/-- In slow exact 3-Nim on 5 piles, the geometric padded witness position has misère invariant 7. -/
theorem op_2051_slow_exact_nim_k3_misere_seven :
    slow_exact_nim_misere 3 5 (slow_exact_nim_geometric_padded_witness 2 3) = 7 := by
  rfl
