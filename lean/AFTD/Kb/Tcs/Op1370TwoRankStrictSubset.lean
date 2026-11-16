import AFTD.Prelude

/-!
# op1370_two_rank_strict_subset

Topic: combinatorics   Node: eca8ff08af9c

Provenance: helper lemma.

A strict inclusion between sets in two consecutive ranks goes from the lower to upper rank and adds one element.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_strict_subset
    {α : Type*} [DecidableEq α] (k : ℕ) (A B : Finset α)
    (hA : A.card = k ∨ A.card = k + 1) (hB : B.card = k ∨ B.card = k + 1)
    (hsub : A ⊆ B) (hne : A ≠ B) :
    A.card = k ∧ B.card = k + 1 ∧ (B \ A).card = 1 := by
  have hle := Finset.card_le_card hsub
  have hnc : A.card ≠ B.card := by
    intro he
    exact hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq he.symm))
  have hd := Finset.card_sdiff_of_subset hsub
  rcases hA with ha | ha <;> rcases hB with hb | hb <;> omega
