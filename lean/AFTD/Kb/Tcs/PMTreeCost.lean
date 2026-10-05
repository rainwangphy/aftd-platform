import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PMTree

/-!
# PMTree.cost

Topic: algorithms   Node: b83ff0b366f5

The number of queries the algorithm T makes on the poset P.
-/

/-- The number of queries the algorithm `T` makes on the poset `P`. -/
def PMTree.cost {n : ℕ} : PMTree n → PMPoset n → ℕ := fun
  | PMTree.leaf _, _ => 0
  | PMTree.node a b k, P => (k (P.ans a b)).cost P + 1
