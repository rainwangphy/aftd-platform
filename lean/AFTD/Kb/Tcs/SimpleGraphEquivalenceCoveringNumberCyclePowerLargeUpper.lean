import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverPullback
import AFTD.Kb.Tcs.CyclePowerFloorMap
import AFTD.Kb.Tcs.CyclePowerFloorMapInduced
import AFTD.Kb.Tcs.CyclePowerInflationParameters
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDvd
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_equivalence_covering_number_cycle_power_large_upper

Topic: combinatorics   Node: 228296500117

Provenance: formalization of a published result. Source: arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For every natural k at least one and natural n at least max(2*k+2, twice the square of k), the equivalence covering number of the k-th power of the cycle on n vertices is at most 2 plus the ceiling of the base-two logarithm of k+1.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_equivalence_covering_number_cycle_power_large_upper
    (k n : ℕ) (hk : 1 ≤ k)
    (hn : max (2*k+2) (2*k^2) ≤ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) ≤
      2+Nat.clog 2 (k+1) := by
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
  unfold simple_graph_equivalence_covering_number
  exact (Nat.sInf_le hpull).trans (by omega)
