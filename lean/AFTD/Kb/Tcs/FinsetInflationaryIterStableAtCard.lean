import AFTD.Prelude

/-!
# finset_inflationary_iter_stable_at_card

Topic: combinatorics   Node: 60e239f65548

Provenance: helper lemma.

An inflationary operation on subsets of a finite n-element set is stationary after n iterations.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN800Inflationary

lemma stable_at_card {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → Finset V) (hf : ∀ S, S ⊆ f S) (S : Finset V) :
    f ((f^[Fintype.card V]) S) = (f^[Fintype.card V]) S := by
  let chain : ℕ → Finset V := fun k => (f^[k]) S
  have hnext (k : ℕ) : chain (k+1) = f (chain k) := by
    simp [chain, Function.iterate_succ_apply']
  have hmono (k : ℕ) : chain k ⊆ chain (k+1) := by rw [hnext]; exact hf _
  by_cases h : ∃ i < Fintype.card V, chain i = chain (i+1)
  · obtain ⟨i, hi, heq⟩ := h
    have hfix : f (chain i) = chain i := by rw [← hnext]; exact heq.symm
    have later : ∀ k, chain (i+k) = chain i := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.add_succ, hnext, ih, hfix]
    have hn : Fintype.card V = i + (Fintype.card V - i) := by omega
    change f (chain (Fintype.card V)) = chain (Fintype.card V)
    rw [hn, later, hfix]
  · have hstrict (i : ℕ) (hi : i < Fintype.card V) :
        (chain i).card < (chain (i+1)).card := by
      apply Finset.card_lt_card
      exact (Finset.ssubset_iff_subset_ne).2 ⟨hmono i, fun heq => h ⟨i, hi, heq⟩⟩
    have hlower : ∀ i ≤ Fintype.card V, i ≤ (chain i).card := by
      intro i hi
      induction i with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        have hp : i < Fintype.card V := by omega
        have hs := hstrict i hp
        have hprev := ih (by omega)
        omega
    have hu : chain (Fintype.card V) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa using hlower (Fintype.card V) le_rfl
    have hfu : f Finset.univ = Finset.univ := by
      apply Finset.Subset.antisymm (Finset.subset_univ _)
      exact hf _
    change f (chain (Fintype.card V)) = chain (Fintype.card V)
    rw [hu, hfu]

end IN800Inflationary

theorem finset_inflationary_iter_stable_at_card {V : Type*} [Fintype V] [DecidableEq V] (f : Finset V → Finset V) (hf : ∀ S, S ⊆ f S) (S : Finset V) : f ((f^[Fintype.card V]) S) = (f^[Fintype.card V]) S := by
  exact IN800Inflationary.stable_at_card f hf S
