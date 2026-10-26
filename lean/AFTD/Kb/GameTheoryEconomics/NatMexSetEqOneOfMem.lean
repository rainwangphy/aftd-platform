import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexSet

/-!
# nat_mex_set_eq_one_of_mem

Topic: combinatorial_games   Node: 0f2f20fdcbf9

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

If 0 is in a set s of natural numbers and 1 is not, the mex of s is 1.
-/

theorem nat_mex_set_eq_one_of_mem {s : Set ℕ} (h0 : 0 ∈ s) (h1 : 1 ∉ s) : nat_mex_set s = 1 := by
  unfold nat_mex_set
  have hne : ({n : ℕ | n ∉ s} : Set ℕ).Nonempty := ⟨1, h1⟩
  have hmem := Nat.sInf_mem hne
  have hle : sInf {n : ℕ | n ∉ s} ≤ 1 := Nat.sInf_le h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
  · rw [h] at hmem; exact absurd h0 hmem
  · exact h
