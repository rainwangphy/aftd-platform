import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt

/-!
# simple_graph_cycle_power_three_adj_iff

Topic: combinatorics   Node: fdd795ca4288

Provenance: helper lemma. Helper for simple_graph_cycle_power_three_cover_three_tight_dvd (thread RT-1, the k = 3 case of OP-205, arXiv:2610.15635).

For n ≥ 10, u and v are adjacent in C_n^3 iff v = u + e for an integer e with 0 < |e| ≤ 3.
-/

theorem simple_graph_cycle_power_three_adj_iff (n : ℕ) [NeZero n] (hn : 10 ≤ n) (u v : ZMod n) :
    (simple_graph_cycle_power n 3).Adj u v ↔ ∃ e : ℤ, e ≠ 0 ∧ |e| ≤ 3 ∧ v = u + e := by
  constructor
  · rintro ⟨huv, hmin⟩
    rcases min_le_iff.mp hmin with h | h
    · refine ⟨-((u - v).val : ℤ), ?_, ?_, ?_⟩
      · intro h0
        have : (u - v).val = 0 := by omega
        rw [ZMod.val_eq_zero, sub_eq_zero] at this
        exact huv this
      · rw [abs_neg, Nat.abs_cast]; exact_mod_cast h
      · push_cast; rw [ZMod.natCast_zmod_val]; ring
    · refine ⟨((v - u).val : ℤ), ?_, ?_, ?_⟩
      · intro h0
        have : (v - u).val = 0 := by omega
        rw [ZMod.val_eq_zero, sub_eq_zero] at this
        exact huv this.symm
      · rw [Nat.abs_cast]; exact_mod_cast h
      · push_cast; rw [ZMod.natCast_zmod_val]; ring
  · rintro ⟨e, he0, he3, rfl⟩
    refine ⟨fun h => he0 ?_, ?_⟩
    · have h' : ((e : ℤ) : ZMod n) = ((0 : ℤ) : ZMod n) := by
        have : (u + e) - u = u - u := by rw [← h]
        simpa using this
      rw [zmod_intCast_eq_intCast_iff_of_abs_sub_lt n e 0 (by simp; omega)] at h'
      exact h'
    · rw [abs_le] at he3
      rcases le_or_gt 0 e with he | he
      · have hv : (u + (e : ZMod n) - u) = ((e.toNat : ℕ) : ZMod n) := by
          simp only [add_sub_cancel_left]
          rw [← Int.toNat_of_nonneg he]; simp
        apply min_le_of_right_le
        rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        omega
      · have hv : (u - (u + (e : ZMod n))) = (((-e).toNat : ℕ) : ZMod n) := by
          have h' : ((-e).toNat : ℤ) = -e := Int.toNat_of_nonneg (by omega)
          rw [sub_add_cancel_left, ← Int.cast_natCast, h']; push_cast; ring
        apply min_le_of_left_le
        rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        omega
