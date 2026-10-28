import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverCyclePowerLargeUpper

/-!
# simple_graph_has_equivalence_cover_cycle_power_dyadic_upper

Topic: combinatorics   Node: 85cd0c173b6e

Provenance: helper lemma. Uniform formal assembly for OP-205 / RT-1 following arXiv:2610.15635 Proposition3.2. The explicit upper covers formalize a published construction. The final reduction keeps the still-unproved pure class-shape theorem as an EXPLICIT additional hypothesis. No unconditional graph covering result or research advance is claimed.

For natural k at least one with k+1 equal to2 to the power m and n at least max(2k+2,twice the square of k), the k-th cycle power on n vertices has an equivalence cover with m+2 layers.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_has_equivalence_cover_cycle_power_dyadic_upper
    (k m n : ℕ) (hk : 1 ≤ k) (hkm : k+1 = 2^m)
    (hn : max (2*k+2) (2*k^2) ≤ n) :
    simple_graph_has_equivalence_cover (simple_graph_cycle_power n k) (m+2) := by
  have hcov := simple_graph_has_equivalence_cover_cycle_power_large_upper k n hk hn
  have hlog : Nat.clog 2 (k+1) ≤ m := Nat.clog_le_of_le_pow hkm.le
  exact simple_graph_has_equivalence_cover_mono (simple_graph_cycle_power n k) (by omega) hcov
