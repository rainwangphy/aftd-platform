import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Quaternary03102HeapOptions

/-!
# quaternary_03102_options

Topic: combinatorial_games   Node: eaa4a12502ab

Provenance: formalization of a published result. Source: arXiv:2611.29198 Section 2.1, 2.4

In the quaternary game 0.3102, the set of follower positions reachable by a legal move on either heap from a two-heap position (x, y).
-/

/-- Options from a two-heap position (x, y) in 0.3102. -/
def quaternary_03102_options (x y : ℕ) : Finset (ℕ × ℕ) :=
  ((quaternary_03102_heap_options x).image (fun x' => (x', y))) ∪
  ((quaternary_03102_heap_options y).image (fun y' => (x, y')))
