import AFTD.Prelude

/-!
# zmod_intCast_eq_intCast_iff_of_abs_sub_lt

Topic: combinatorics   Node: 75636e634b1d

Provenance: helper lemma. Helper for simple_graph_cycle_power_three_cover_three_tight_dvd (thread RT-1, the k = 3 case of OP-205, arXiv:2610.15635).

Two integers a, b with |a − b| < n are equal modulo n only if they are equal.
-/

theorem zmod_intCast_eq_intCast_iff_of_abs_sub_lt (n : ℕ) (a b : ℤ) (h : |a - b| < n) :
    ((a : ZMod n) = (b : ZMod n)) ↔ a = b := by
  refine ⟨fun hab => ?_, fun hab => hab ▸ rfl⟩
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hab
  have := Int.eq_zero_of_abs_lt_dvd hab (by rwa [abs_sub_comm])
  omega
