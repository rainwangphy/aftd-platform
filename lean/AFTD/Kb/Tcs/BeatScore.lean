import AFTD.Prelude
import AFTD.Kb.Tcs.Die
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# beat_score

Topic: combinatorics   Node: fc1aa38e26fa

Provenance: formalization of a published result. Source: arXiv:2610.40321 Eq 3

The beat score of die x against die y, defined as the sum over all face indices i and j in Fin n of 1 if x(i) > y(j) and 0 otherwise.
-/

/-- Number of face pairs where die x strictly beats die y. -/
def beat_score {n : ℕ} (x y : Die n) : ℕ := ∑ i : Fin n, ∑ j : Fin n, if x.1 i > y.1 j then 1 else 0
