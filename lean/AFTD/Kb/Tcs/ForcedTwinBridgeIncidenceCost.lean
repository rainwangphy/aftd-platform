import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# forced_twin_bridge_incidence_cost

Topic: graphs   Node: 0e7373a646cb

Provenance: helper lemma. OP-1957 first-forced-edge and second-bridge weighted incidence budget; experiment 35715 tests the arithmetic, and the proof passed scratch Lean.

For a shore of size at least four, an opposite shore with at least three external vertices, and an internal edge budget covering the first forced edge and the shore biclique, the combined internal and excess external incidence cost is at least seven halves of the first-shore size minus two.
-/

theorem forced_twin_bridge_incidence_cost (m w s r e : ℤ) (hw : 4 ≤ w) (hs : 0 ≤ s) (hr : 3 ≤ r) (hsum : m + 2 = w + s + r) (hcover : m - 2 ≤ e) (hcross : s*w ≤ e) : 7*(m-2) ≤ 4*e + 2*r*(w-2) := by
  have hprod : 0 ≤ (w-4)*(s+2*r-4) :=
    mul_nonneg (by omega) (by omega)
  nlinarith
