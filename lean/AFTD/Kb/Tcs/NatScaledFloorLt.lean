import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# nat_scaled_floor_lt

Topic: combinatorics   Node: c0dd9a5cb33d

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For positive natural n and N, and natural i less than n, floor(i*N/n) is less than N.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem nat_scaled_floor_lt
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (i : ℕ) (hi : i < n) : i*N/n < N := by
  apply (Nat.div_lt_iff_lt_mul hn).mpr
  have hprod := Nat.mul_lt_mul_of_pos_right hi hN
  nlinarith
