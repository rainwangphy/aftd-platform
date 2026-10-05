import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PMPosetMinSet
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeRun

/-!
# PMTree.Correct2

Topic: algorithms   Node: f6c6ab88b6c7

T correctly finds the minimal elements of every poset of width at most 2 on Fin n.
-/

/-- `T` correctly finds the minimal elements of every poset of width at most `2` on `Fin n`. -/
def PMTree.Correct2 {n : ℕ} (T : PMTree n) : Prop :=
  ∀ P : PMPoset n, P.Width2 → T.run P = P.minSet
