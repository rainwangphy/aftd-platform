import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexSet

/-!
# nat_mex_set_eq_zero_of_not_mem

Topic: combinatorial_games   Node: 0a0151bc0238

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

If 0 is not in a set s of natural numbers, the mex of s is 0.
-/

theorem nat_mex_set_eq_zero_of_not_mem {s : Set ℕ} (h : 0 ∉ s) : nat_mex_set s = 0 := by
  unfold nat_mex_set
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using h))
