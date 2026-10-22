import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyStep

/-!
# greedyMatching

Topic: online_algorithms   Node: 7e9f193af86f

Provenance: formalization of a published result. Source: arXiv:2610.23130, Section 1

Given a predicate P : Finset (Sym2 (ℝ × ℝ)) → Prop and an input list of points pts : List (ℝ × ℝ), greedyMatching folds greedyStep P across pts starting from the empty matching ∅ : Finset (Sym2 (ℝ × ℝ)) and empty unmatched list [].
-/

/-- The greedy online geometric matching algorithm on an input sequence of points. -/
noncomputable def greedyMatching (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (pts : List (ℝ × ℝ)) :
    Finset (Sym2 (ℝ × ℝ)) × List (ℝ × ℝ) := pts.foldl (greedyStep P) (∅, [])
