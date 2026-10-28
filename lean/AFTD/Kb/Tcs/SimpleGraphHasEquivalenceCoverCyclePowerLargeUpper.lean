import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverPullback
import AFTD.Kb.Tcs.CyclePowerFloorMap
import AFTD.Kb.Tcs.CyclePowerFloorMapInduced
import AFTD.Kb.Tcs.CyclePowerInflationParameters
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDvd
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_has_equivalence_cover_cycle_power_large_upper

Topic: combinatorics   Node: 3011d11b47fd

Provenance: helper lemma. Uniform formal assembly for OP-205 / RT-1 following arXiv:2610.15635 Proposition3.2. The explicit upper covers formalize a published construction. The final reduction keeps the still-unproved pure class-shape theorem as an EXPLICIT additional hypothesis. No unconditional graph covering result or research advance is claimed.

For natural k at least one and n at least max(2k+2,twice the square of k), the k-th cycle power on n vertices has an equivalence cover with2 plus the ceiling base-two logarithm of k+1 layers.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_has_equivalence_cover_cycle_power_large_upper
    (k n : ℕ) (hk : 1 ≤ k)
    (hn : max (2*k+2) (2*k^2) ≤ n) :
    simple_graph_has_equivalence_cover (simple_graph_cycle_power n k)
      (2+Nat.clog 2 (k+1)) := by
  have hn₀ : 2*k+2 ≤ n := (le_max_left _ _).trans hn
  have hn₂ : 2*k^2 ≤ n := (le_max_right _ _).trans hn
  let q := (n+k)/(k+1)
  have hp := cycle_power_inflation_parameters n k hk hn₀ hn₂
  change 2 ≤ q ∧ n ≤ q*(2*k+1) ∧ q*(2*k+1) ≤ 2*n ∧
    (2*k+1)*n ≤ (k+1)*(q*(2*k+1)) at hp
  let N := q*(2*k+1)
  have hemb := cycle_power_floor_map_induced n N k (2*k) (by omega) hp.2.1
    (by dsimp [N]; nlinarith [hp.2.2.1]) hp.2.2.2
  have hcov := simple_graph_equivalence_covering_number_cycle_power_dvd_cover (2*k) q
    (by omega) hp.1
  have hpull := simple_graph_has_equivalence_cover_pullback
    (simple_graph_cycle_power n k) (simple_graph_cycle_power N (2*k))
    (1+Nat.clog 2 (2*k+1)) (cycle_power_floor_map n N) hemb.1 hemb.2 hcov
  have hlog : Nat.clog 2 (2*k+1) ≤ Nat.clog 2 (k+1)+1 := by
    apply Nat.clog_le_of_le_pow
    have hbase : k+1 ≤ 2^(Nat.clog 2 (k+1)) :=
      (Nat.clog_le_iff_le_pow (by decide)).mp le_rfl
    rw [pow_succ]
    omega
  exact simple_graph_has_equivalence_cover_mono (simple_graph_cycle_power n k) (by omega) hpull
