import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTree

/-!
# TarskiQueryTree.run

Topic: algorithms   Node: ed0ba78f9270

Provenance: formalization of a published result. Source: arXiv:2610.07055 (Tarski fixed points in quasi-FPT queries), Sec. 1

The point a query tree outputs when the black box is f.
-/

/-- The point a query tree outputs when the black box is `f`. -/
def TarskiQueryTree.run {n k : ℕ} (f : (Fin k → Fin n) → (Fin k → Fin n)) :
    TarskiQueryTree n k → (Fin k → Fin n) := fun
  | .output x => x
  | .query x next => (next (f x)).run f
