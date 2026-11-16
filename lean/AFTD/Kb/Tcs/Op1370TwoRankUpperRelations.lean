import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370TwoRankStrictSubset

/-!
# op1370_two_rank_upper_relations

Topic: combinatorics   Node: e233db23097c

Provenance: helper lemma.

For an upper-rank set, its strict neighbors in the comparability graph are exactly its lower-rank subsets.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_upper_relations
    {α V : Type*} [DecidableEq α] (k : ℕ) (A : V → Finset α)
    (hA : Function.Injective A) (levels : ∀ a, (A a).card = k ∨ (A a).card = k + 1)
    (G : SimpleGraph V) (hAdj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (A a ⊆ A b ∨ A b ⊆ A a))
    (x : V) (hx : (A x).card = k + 1) :
    (∀ a, A a ⊆ A x ↔ a = x ∨ G.Adj x a) ∧
    (∀ a, A x ⊆ A a ↔ a = x) ∧
    (∀ a, G.Adj x a → ((A x) \ (A a)).card = 1) := by
  have hsup (a : V) (hsub : A x ⊆ A a) : a = x := by
    by_contra hne
    have hs := op1370_two_rank_strict_subset k (A x) (A a)
      (levels x) (levels a) hsub (fun h => hne (hA h).symm)
    omega
  have hadj_sub (a : V) (ha : G.Adj x a) : A a ⊆ A x := by
    rcases (hAdj x a).mp ha with ⟨hne, hsub | hsub⟩
    · exact (hne (hsup a hsub).symm).elim
    · exact hsub
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · intro hsub
      by_cases h : a = x
      · exact Or.inl h
      · exact Or.inr ((hAdj x a).mpr ⟨Ne.symm h, Or.inr hsub⟩)
    · rintro (rfl | ha)
      · exact Finset.Subset.rfl
      · exact hadj_sub a ha
  · intro a
    constructor
    · exact hsup a
    · rintro rfl
      exact Finset.Subset.rfl
  · intro a ha
    have hne : A a ≠ A x := fun h => ((hAdj x a).mp ha).1 (hA h).symm
    exact (op1370_two_rank_strict_subset k (A a) (A x)
      (levels a) (levels x) (hadj_sub a ha) hne).2.2
