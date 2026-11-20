import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# selected_shore_incidence_cost

Topic: graphs   Node: 7da2e1afe60d

Provenance: helper lemma. Weighted incidence budget in the OP-1957 saturated-twin branch; experiment 35729 checks the arithmetic, and the exact proof passed scratch Lean.

If the first shore has size m, the second shore has size w between four and m−2, and the opposite shore meets the first shore in at most one vertex, then the first internal-cover cost plus the external-shore and selected-endpoint costs are at least 4m−9.
-/

theorem selected_shore_incidence_cost (m w s r : ℤ) (hw : 4 ≤ w) (hwm : w ≤ m-2) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hsum : m+2 = w+s+r) : 4*m-9 ≤ 2*(m-2)+r*(w-2)+s := by
  have hprod : 0 ≤ (w-4)*(m-w-1) :=
    mul_nonneg (by omega) (by omega)
  have hprod' : 0 ≤ (1-s)*(w-3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith
