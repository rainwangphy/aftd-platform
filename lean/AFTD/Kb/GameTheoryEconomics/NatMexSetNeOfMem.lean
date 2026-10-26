import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexSet

/-!
# nat_mex_set_ne_of_mem

Topic: combinatorial_games   Node: 53a6e347ae49

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

The mex of a finite set s of natural numbers is not an element of s.
-/

theorem nat_mex_set_ne_of_mem {s : Set ℕ} (hs : s.Finite) {k : ℕ} (hk : k ∈ s) : nat_mex_set s ≠ k := by
  unfold nat_mex_set
  intro h
  have hne : ({n : ℕ | n ∉ s} : Set ℕ).Nonempty := hs.infinite_compl.nonempty
  have hmem := Nat.sInf_mem hne
  rw [h] at hmem
  exact hmem hk
