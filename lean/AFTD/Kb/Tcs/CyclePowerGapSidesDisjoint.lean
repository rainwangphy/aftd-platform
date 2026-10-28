import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide

/-!
# cycle_power_gap_sides_disjoint

Topic: combinatorics   Node: 768edeffb933

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

The lower and upper sides of a rooted gap profile are disjoint because their compressed vertex coordinates lie on opposite sides of the root.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_gap_sides_disjoint (D g r : ℕ) (b : ℕ → Bool) :
    Disjoint (cycle_power_gap_left_side g r b) (cycle_power_gap_right_side D g r b) := by
  apply disjoint_left.mpr
  intro i hi hj
  have hri := (mem_filter.mp hi).2.1
  have hir := (mem_filter.mp hj).2.1
  omega
