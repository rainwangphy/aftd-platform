import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.NatScaledFloorGapThreshold
import AFTD.Kb.Tcs.NatScaledFloorStrict
import AFTD.Kb.Tcs.NatScaledFloorLt
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffValLt
import AFTD.Kb.Tcs.CyclePowerFloorMap

/-!
# cycle_power_floor_map_induced

Topic: combinatorics   Node: e7b287e574e2

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For natural n,N,k,K with n positive, N at least n, k*N at most K*n, and (K+1)*n at most (k+1)*N, the balanced floor map from ZMod n to ZMod N is injective and preserves and reflects adjacency from the k-th cycle power to the K-th cycle power.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_floor_map_induced
    (n N k K : ℕ) (hn : 0 < n) (hN : n ≤ N)
    (hlo : k*N ≤ K*n) (hhi : (K+1)*n ≤ (k+1)*N) :
    Function.Injective (cycle_power_floor_map n N) ∧
      ∀ u v : ZMod n, (simple_graph_cycle_power n k).Adj u v ↔
        (simple_graph_cycle_power N K).Adj (cycle_power_floor_map n N u) (cycle_power_floor_map n N v) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero N := ⟨by omega⟩
  have hN₀ : 0 < N := by omega
  have hval (u : ZMod n) : (cycle_power_floor_map n N u).val = u.val*N/n :=
    ZMod.val_cast_of_lt (nat_scaled_floor_lt n N hn hN₀ u.val (ZMod.val_lt u))
  have hinj : Function.Injective (cycle_power_floor_map n N) := by
    intro u v he
    apply ZMod.val_injective
    have heval := congrArg ZMod.val he
    rw [hval u, hval v] at heval
    rcases lt_trichotomy u.val v.val with h | h | h
    · have := nat_scaled_floor_strict n N hn hN u.val v.val h
      omega
    · exact h
    · have := nat_scaled_floor_strict n N hn hN v.val u.val h
      omega
  have hlt (u v : ZMod n) (huv : u.val < v.val) :
      (simple_graph_cycle_power n k).Adj u v ↔
        (simple_graph_cycle_power N K).Adj (cycle_power_floor_map n N u) (cycle_power_floor_map n N v) := by
    have ht : (cycle_power_floor_map n N u).val < (cycle_power_floor_map n N v).val := by
      rw [hval u, hval v]
      exact nat_scaled_floor_strict n N hn hN u.val v.val huv
    rw [simple_graph_cycle_power_adj_iff_val_lt n k u v huv,
      simple_graph_cycle_power_adj_iff_val_lt N K _ _ ht, hval u, hval v]
    have hfirst := nat_scaled_floor_gap_threshold n N k K hn hlo hhi u.val v.val huv.le
    have hwrap := nat_scaled_floor_gap_threshold n N k K hn hlo hhi v.val (u.val+n)
      (by have := ZMod.val_lt v; omega)
    have hperiod : (u.val+n)*N/n = u.val*N/n+N := by
      rw [Nat.add_mul]
      rw [Nat.add_mul_div_left _ _ hn]
    rw [hperiod] at hwrap
    have he₀ : u.val+n-v.val = n-(v.val-u.val) := by have := ZMod.val_lt v; omega
    have he₁ : u.val*N/n+N-v.val*N/n = N-(v.val*N/n-u.val*N/n) := by
      have h₀ := nat_scaled_floor_lt n N hn hN₀ v.val (ZMod.val_lt v)
      have h₁ := nat_scaled_floor_strict n N hn hN u.val v.val huv
      omega
    rw [he₀, he₁] at hwrap
    exact or_congr hfirst hwrap
  refine ⟨hinj, ?_⟩
  intro u v
  rcases lt_trichotomy u.val v.val with h | h | h
  · exact hlt u v h
  · have he : u = v := ZMod.val_injective n h
    subst v
    simp only [SimpleGraph.irrefl]
  · have he := hlt v u h
    simpa only [SimpleGraph.adj_comm] using he
