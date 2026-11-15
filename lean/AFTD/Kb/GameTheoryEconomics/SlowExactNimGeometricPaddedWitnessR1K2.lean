import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGeometricPaddedWitness
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundy

/-!
# slow_exact_nim_geometric_padded_witness_r1_k2

Topic: combinatorial_games   Node: 005ce0fcb458

Provenance: helper lemma. arXiv:2611.14546; OP-1728

In slow exact 2-Nim on 3 piles, the Sprague-Grundy value of the geometric padded witness position slow_exact_nim_geometric_padded_witness 1 2 equals 3.
-/

/-- The Sprague-Grundy value of the geometric padded witness for r = 1, k = 2 is 3. -/
theorem slow_exact_nim_geometric_padded_witness_r1_k2 :
    slow_exact_nim_grundy 2 (2 + 1) (slow_exact_nim_geometric_padded_witness 1 2) = 3 := rfl
