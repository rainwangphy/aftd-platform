import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGeometricPaddedWitness
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundy

/-!
# slow_exact_nim_geometric_padded_witness_r2_k3

Topic: combinatorial_games   Node: b46e5e7ebdf3

Provenance: helper lemma. arXiv:2611.14546; OP-1728

In slow exact 3-Nim on 5 piles, the Sprague-Grundy value of the geometric padded witness position slow_exact_nim_geometric_padded_witness 2 3 equals 7.
-/

/-- The Sprague-Grundy value of the geometric padded witness for r = 2, k = 3 is 7. -/
theorem slow_exact_nim_geometric_padded_witness_r2_k3 :
    slow_exact_nim_grundy 3 (3 + 2) (slow_exact_nim_geometric_padded_witness 2 3) = 7 := rfl
