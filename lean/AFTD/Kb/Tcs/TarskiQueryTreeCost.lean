import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTree

/-!
# TarskiQueryTree.cost

Topic: algorithms   Node: ab291dbc82fe

Provenance: formalization of a published result. Source: arXiv:2610.07055 (Tarski fixed points in quasi-FPT queries), Sec. 1

The number of queries a query tree makes when the black box is f (the length of the path f follows).
-/

/-- The number of queries a query tree makes when the black box is `f`. -/
def TarskiQueryTree.cost {n k : ℕ} (f : (Fin k → Fin n) → (Fin k → Fin n)) :
    TarskiQueryTree n k → ℕ := fun
  | .output _ => 0
  | .query x next => (next (f x)).cost f + 1
