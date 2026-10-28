import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_cycle_power_adj_iff_val_lt

Topic: combinatorics   Node: 8ec4bed874c0

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

For a nonzero natural n, natural k, and vertices u,v of ZMod n with u.val less than v.val, adjacency in the k-th cycle power is equivalent to either v.val-u.val at most k or n-(v.val-u.val) at most k.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_cycle_power_adj_iff_val_lt
    (n k : ℕ) [NeZero n] (u v : ZMod n) (huv : u.val < v.val) :
    (simple_graph_cycle_power n k).Adj u v ↔
      v.val-u.val ≤ k ∨ n-(v.val-u.val) ≤ k := by
  have hne : u ≠ v := by intro h; have := congrArg ZMod.val h; omega
  have hdiff : (v-u).val = v.val-u.val := ZMod.val_sub huv.le
  have hdiffnz : v-u ≠ 0 := by intro h; exact hne (sub_eq_zero.mp h).symm
  have hneg : (u-v).val = n-(v-u).val := by
    rw [← neg_sub v u]
    letI : NeZero (v-u) := ⟨hdiffnz⟩
    exact ZMod.val_neg_of_ne_zero (v-u)
  change (u ≠ v ∧ min (u-v).val (v-u).val ≤ k) ↔ _
  rw [hneg, hdiff, min_le_iff]
  constructor
  · intro h
    exact h.2.symm
  · intro h
    exact ⟨hne, h.symm⟩
