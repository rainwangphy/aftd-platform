import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange

/-!
# postage_stamp_basis_range_succ_le_card_pow

Topic: elementary_number_theory   Node: c24d1297fec0

Provenance: helper lemma. Helper for arXiv:2610.19470 (Positivity and negativity for h-bases for n) (the extremal functions n_h(k), n♭_h(k) are finite maxima).

If A is a nonempty finite set of integers, n_h(A) + 1 ≤ |A|^h: the integers 0, ..., n_h(A) are distinct elements of hA, which has at most |A|^h elements.
-/

open scoped BigOperators
open Finset

def postage_stamp_basis_range_succ_le_card_pow_hFoldSumsetFinset (h : ℕ) (A : Finset ℤ) : Finset ℤ :=
  (Fintype.piFinset fun _ : Fin h => A).image (fun f => ∑ i, f i)

lemma postage_stamp_basis_range_succ_le_card_pow_mem_hFoldSumsetFinset (h : ℕ) (A : Finset ℤ) (z : ℤ) :
    z ∈ postage_stamp_basis_range_succ_le_card_pow_hFoldSumsetFinset h A ↔ int_mem_h_fold_sumset h A z := by
  simp [postage_stamp_basis_range_succ_le_card_pow_hFoldSumsetFinset, int_mem_h_fold_sumset]

lemma postage_stamp_basis_range_succ_le_card_pow_card_hFoldSumsetFinset_le (h : ℕ) (A : Finset ℤ) :
    (postage_stamp_basis_range_succ_le_card_pow_hFoldSumsetFinset h A).card ≤ A.card ^ h := by
  calc (postage_stamp_basis_range_succ_le_card_pow_hFoldSumsetFinset h A).card
    _ ≤ (Fintype.piFinset fun _ : Fin h => A).card := card_image_le
    _ = A.card ^ h := by simp

lemma postage_stamp_basis_range_succ_le_card_pow_card_range_image_le (h : ℕ) (A : Finset ℤ) (n : ℕ)
    (hn : ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h A m) :
    n + 1 ≤ A.card ^ h := by
  have hsub : ((range (n + 1)).image (fun (m : ℕ) => (m : ℤ))) ⊆
      postage_stamp_basis_range_succ_le_card_pow_hFoldSumsetFinset h A := by
    intro x hx
    simp only [mem_image, mem_range] at hx
    rcases hx with ⟨m, hm, rfl⟩
    rw [postage_stamp_basis_range_succ_le_card_pow_mem_hFoldSumsetFinset]
    exact hn m (Nat.lt_succ_iff.mp hm)
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ Nat.cast_injective, card_range] at hcard
  exact hcard.trans (postage_stamp_basis_range_succ_le_card_pow_card_hFoldSumsetFinset_le h A)

theorem postage_stamp_basis_range_succ_le_card_pow (h : ℕ) (A : Finset ℤ) (hA : A.Nonempty) :
    postage_stamp_basis_range h A + 1 ≤ A.card ^ h := by
  let S := {n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h A m}
  change sSup S + 1 ≤ A.card ^ h
  by_cases hS : S.Nonempty
  · have hBdd : BddAbove S := by
      use A.card ^ h
      intro n hn
      exact le_trans (Nat.le_succ n) (postage_stamp_basis_range_succ_le_card_pow_card_range_image_le h A n hn)
    have hmem : sSup S ∈ S := Nat.sSup_mem hS hBdd
    exact postage_stamp_basis_range_succ_le_card_pow_card_range_image_le h A (sSup S) hmem
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [hS, csSup_empty]
    have hpos : 0 < A.card := Finset.Nonempty.card_pos hA
    exact Nat.one_le_pow h A.card hpos
