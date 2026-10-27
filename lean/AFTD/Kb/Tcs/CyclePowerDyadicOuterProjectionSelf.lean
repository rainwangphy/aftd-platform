import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection

/-!
# cycle_power_dyadic_outer_projection_self

Topic: combinatorics   Node: 50d550c2bc5d

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

At its original radius, direct outer projection is the identity on every offset.
-/

open Finset

theorem cycle_power_dyadic_outer_projection_self (r : ℕ) (b : ℕ → Bool) :
    cycle_power_dyadic_outer_projection (r+1) r b = b := by
  funext a
  simp [cycle_power_dyadic_outer_projection]
