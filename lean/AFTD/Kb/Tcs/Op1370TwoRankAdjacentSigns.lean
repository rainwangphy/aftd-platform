import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370TwoRankStrictSubset

/-!
# op1370_two_rank_adjacent_signs

Topic: combinatorics   Node: f21a6bf80d5c

Provenance: helper lemma.

In adjacent ranks, comparable distinct sets have opposite alternating signs.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_adjacent_signs
    {α V : Type*} [DecidableEq α] (n k : ℕ) (A : V → Finset α)
    (hA : Function.Injective A) (levels : ∀ a, (A a).card = k ∨ (A a).card = k + 1)
    (hbound : ∀ a, (A a).card ≤ n)
    (G : SimpleGraph V) (hAdj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (A a ⊆ A b ∨ A b ⊆ A a)) :
    ∀ x a, G.Adj x a →
      (-1 : ℚ) ^ (n - (A a).card) = -((-1 : ℚ) ^ (n - (A x).card)) := by
  intro x a ha
  rcases (hAdj x a).mp ha with ⟨hne, hsub | hsub⟩
  · have hsets : A x ≠ A a := fun h => hne (hA h)
    obtain ⟨hx, ha, hd⟩ := op1370_two_rank_strict_subset k (A x) (A a)
      (levels x) (levels a) hsub hsets
    have hb := hbound a
    have he : n - (A x).card = (n - (A a).card) + 1 := by omega
    rw [he, pow_succ]
    simp
  · have hsets : A a ≠ A x := fun h => hne (hA h).symm
    obtain ⟨ha, hx, hd⟩ := op1370_two_rank_strict_subset k (A a) (A x)
      (levels a) (levels x) hsub hsets
    have hb := hbound x
    have he : n - (A a).card = (n - (A x).card) + 1 := by omega
    rw [he, pow_succ]
    simp
