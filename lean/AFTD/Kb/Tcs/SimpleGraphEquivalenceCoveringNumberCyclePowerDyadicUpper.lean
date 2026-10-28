import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerLargeUpper

/-!
# simple_graph_equivalence_covering_number_cycle_power_dyadic_upper

Topic: combinatorics   Node: 3a36cfd3b714

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For natural k,m,n with k at least one, k+1 equal to 2 to the power m, and n at least max(2*k+2, twice the square of k), the equivalence covering number of the k-th power of the cycle on n vertices is at most m+2.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_equivalence_covering_number_cycle_power_dyadic_upper
    (k m n : ℕ) (hk : 1 ≤ k) (hkm : k+1 = 2^m)
    (hn : max (2*k+2) (2*k^2) ≤ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) ≤ m+2 := by
  have hu := simple_graph_equivalence_covering_number_cycle_power_large_upper k n hk hn
  have hlog : Nat.clog 2 (k+1) ≤ m := Nat.clog_le_of_le_pow hkm.le
  omega
