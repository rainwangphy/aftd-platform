import AFTD.Prelude

/-!
# op1370_boolean_interval_cancellation

Topic: combinatorics   Node: de33be5d63ce

Provenance: helper lemma.

The alternating sum over a Boolean interval is one for equal endpoints and zero otherwise.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_boolean_interval_cancellation
    {α : Type*} [DecidableEq α] (A B : Finset α) (hAB : A ⊆ B) :
    (∑ X ∈ Finset.Icc A B, (-1 : ℤ) ^ (X \ A).card) = if A = B then 1 else 0 := by
  classical
  have hd (Y : Finset α) (hY : Y ∈ (B \ A).powerset) : Disjoint A Y :=
    Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hY) Finset.disjoint_sdiff
  rw [Finset.Icc_eq_image_powerset hAB, Finset.sum_image]
  · calc
      (∑ Y ∈ (B \ A).powerset, (-1 : ℤ) ^ ((A ∪ Y) \ A).card) =
          ∑ Y ∈ (B \ A).powerset, (-1 : ℤ) ^ Y.card := by
            apply Finset.sum_congr rfl
            intro Y hY
            rw [Finset.union_sdiff_cancel_left (hd Y hY)]
      _ = if B \ A = ∅ then 1 else 0 := Finset.sum_powerset_neg_one_pow_card
      _ = if A = B then 1 else 0 := by
        by_cases h : A = B
        · subst B
          simp
        · have hn : B \ A ≠ ∅ := by
            intro he
            have hBA : B ⊆ A := Finset.sdiff_eq_empty_iff_subset.mp he
            exact h (Finset.Subset.antisymm hAB hBA)
          simp [h, hn]
  · intro Y hY Z hZ h
    have hh := congrArg (fun X : Finset α => X \ A) h
    simpa only [Finset.union_sdiff_cancel_left (hd Y hY),
      Finset.union_sdiff_cancel_left (hd Z hZ)] using hh
