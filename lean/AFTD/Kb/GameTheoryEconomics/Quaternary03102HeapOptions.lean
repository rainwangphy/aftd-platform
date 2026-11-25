import AFTD.Prelude

/-!
# quaternary_03102_heap_options

Topic: combinatorial_games   Node: addf2557f316

Provenance: formalization of a published result. Source: arXiv:2611.29198 Section 2.4

In the quaternary game 0.3102, the set of heap sizes reachable by a legal move on a single heap of size h (removal of sizes 1 and 2, subtraction of 1 when h > 1 and 4 when h > 4).
-/

/-- Options for a single heap of size h in the quaternary game 0.3102. -/
def quaternary_03102_heap_options (h : ℕ) : Finset ℕ :=
  (if h = 1 ∨ h = 2 then {0} else ∅) ∪
  (if 1 < h then {h - 1} else ∅) ∪
  (if 4 < h then {h - 4} else ∅)
