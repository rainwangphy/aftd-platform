import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns

/-!
# PMTree

Topic: algorithms   Node: 63c2c40a56cb

A deterministic adaptive comparison algorithm, as a decision tree: a leaf outputs a set, an internal node queries the pair (a, b) and branches on the answer.
-/

/-- A deterministic adaptive comparison algorithm, as a decision tree: a leaf outputs a set, an internal node queries the pair `(a, b)` and branches on the answer. -/
inductive PMTree (n : ℕ) | leaf : Finset (Fin n) → PMTree n
  | node : Fin n → Fin n → (PMAns → PMTree n) → PMTree n
