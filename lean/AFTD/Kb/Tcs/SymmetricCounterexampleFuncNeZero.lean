import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricCounterexampleFunc

/-!
# symmetric_counterexample_func_ne_zero

Topic: combinatorics   Node: e096d59440d6

Provenance: formalization of a published result. Source: arXiv:2611.06744, Corollary 1

For every natural number n, the symmetric Boolean function symmetric_counterexample_func n is not identically zero.
-/

/-- The symmetric Boolean function F_n is nonzero for every n. -/
theorem symmetric_counterexample_func_ne_zero (n : ℕ) : symmetric_counterexample_func n ≠ 0 := by
  intro h
  have key : symmetric_counterexample_func n (fun _ => (0 : ZMod 2)) = 1 := by
    unfold symmetric_counterexample_func
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj h0
      rw [Finset.sum_eq_zero]
      intro s hs
      rw [Finset.prod_eq_zero_iff]
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨_, hcard⟩ := hs
      have : s.Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi, rfl⟩
    · intro h; simp at h
  rw [h] at key
  simp at key
