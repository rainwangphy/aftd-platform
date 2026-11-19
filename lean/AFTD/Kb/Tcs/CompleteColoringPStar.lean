import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteColoringB

/-!
# complete_coloring_p_star

Topic: quantum   Node: 902181456209

Provenance: formalization of a published result. Source: arXiv:2611.19002, Quantum Coloring Games on Complete Graphs, Section 3.4

The conjectured classical synchrony threshold p_* = (B - 1) / (n + B - 2) in the complete-graph coloring game.
-/

/-- The classical synchrony threshold p_* = (B - 1) / (n + B - 2). -/
def complete_coloring_p_star (n m : ℕ) : ℚ :=
  let B := complete_coloring_B n m
  (B - 1) / ((n : ℚ) + B - 2)
