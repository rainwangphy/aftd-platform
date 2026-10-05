import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PMTree

/-!
# PMTree.run

Topic: algorithms   Node: 5d14aa0a304b

The output of the algorithm T on the poset P.
-/

open Finset in
/-- The output of the algorithm `T` on the poset `P`. -/
def PMTree.run {n : ℕ} : PMTree n → PMPoset n → Finset (Fin n) := fun
  | PMTree.leaf s, _ => s
  | PMTree.node a b k, P => (k (P.ans a b)).run P
