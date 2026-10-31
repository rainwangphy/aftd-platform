import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Die

Topic: combinatorics   Node: f0b9c6731eaa

Provenance: formalization of a published result. Source: arXiv:2610.40321 Def 1

The type of non-standard n-sided dice with face values in Fin n, represented as non-decreasing functions from Fin n to Fin n.
-/

/-- Non-standard n-sided dice represented as non-decreasing tuples in Fin n. -/
def Die (n : ℕ) : Type := { d : Fin n → Fin n // Monotone d }
