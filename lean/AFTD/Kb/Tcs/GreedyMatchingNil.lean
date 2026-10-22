import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyMatching

/-!
# greedyMatching_nil

Topic: online_algorithms   Node: c517655b99cb

Provenance: helper lemma. arXiv:2610.23130, Section 1

For every predicate P : Finset (Sym2 (ℝ × ℝ)) → Prop on finite sets of unordered pairs of points in ℝ × ℝ, greedyMatching P [] equals the pair (∅, []).
-/

/-- Greedy matching on the empty sequence produces an empty matching and empty unmatched list. -/
theorem greedyMatching_nil (P : Finset (Sym2 (ℝ × ℝ)) → Prop) : greedyMatching P [] = (∅, []) := by
  simp [greedyMatching]
