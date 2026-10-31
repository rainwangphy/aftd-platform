import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# order_pos

Topic: combinatorics   Node: 981384027a35

Provenance: formalization of a published result. Source: arXiv:2610.39311 Section 2

The 1-based position of attribute a in order π, taking values in {1, ..., d}.
-/

/-- 1-based position of attribute a in order π. -/
def order_pos {d : ℕ} (π : Order d) (a : Fin d) : ℕ := π.elems.idxOf a + 1
