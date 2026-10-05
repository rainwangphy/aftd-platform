import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns

/-!
# PMState

Topic: algorithms   Node: c713c0301d59

The state of the adversary: a colouring (which of the two chains), ranks, a component label, the set of "alive" elements (not yet shown to have anything below them), and the list of answered queries.
-/

/-- The state of the adversary: a colouring (which of the two chains), ranks, a component label, the set of "alive" elements (not yet shown to have anything below them), and the list of answered queries. -/
structure PMState (n : ℕ) where
  col : Fin n → Bool
  rk : Fin n → ℤ
  comp : Fin n → Fin n
  alive : Finset (Fin n)
  facts : List (Fin n × Fin n × PMAns)
