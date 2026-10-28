import AFTD.Prelude

/-!
# cycle_power_gap_right_side

Topic: combinatorics   Node: 71e2252f1c08

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

The upper-block vertices of a rooted profile, represented in Fin g after subtracting the radius.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def cycle_power_gap_right_side (D g r : ℕ) (b : ℕ → Bool) : Finset (Fin g) := by
  exact univ.filter (fun i => i.val < r ∧ b (D+i.val-r) = true)
