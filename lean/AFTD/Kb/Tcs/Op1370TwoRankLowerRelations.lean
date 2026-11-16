import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370TwoRankStrictSubset

/-!
# op1370_two_rank_lower_relations

Topic: combinatorics   Node: eb591d5f2961

Provenance: helper lemma.

For a lower-rank set, its strict neighbors in the comparability graph are exactly its upper-rank supersets.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_lower_relations
    {α V : Type*} [DecidableEq α] (k : ℕ) (A : V → Finset α)
    (hA : Function.Injective A) (levels : ∀ a, (A a).card = k ∨ (A a).card = k + 1)
    (G : SimpleGraph V) (hAdj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (A a ⊆ A b ∨ A b ⊆ A a))
    (x : V) (hx : (A x).card = k) :
    (∀ a, A a ⊆ A x ↔ a = x) ∧
    (∀ a, A x ⊆ A a ↔ a = x ∨ G.Adj x a) ∧
    (∀ a, G.Adj x a → ((A a) \ (A x)).card = 1) := by
  have hsub (a : V) (hle : A a ⊆ A x) : a = x := by
    by_contra hne
    have hs := op1370_two_rank_strict_subset k (A a) (A x)
      (levels a) (levels x) hle (fun h => hne (hA h))
    omega
  have hadj_sup (a : V) (ha : G.Adj x a) : A x ⊆ A a := by
    rcases (hAdj x a).mp ha with ⟨hne, hle | hle⟩
    · exact hle
    · exact (hne (hsub a hle).symm).elim
  refine ⟨?_, ?_, ?_⟩
  · intro a
    constructor
    · exact hsub a
    · rintro rfl
      exact Finset.Subset.rfl
  · intro a
    constructor
    · intro hle
      by_cases h : a = x
      · exact Or.inl h
      · exact Or.inr ((hAdj x a).mpr ⟨Ne.symm h, Or.inl hle⟩)
    · rintro (rfl | ha)
      · exact Finset.Subset.rfl
      · exact hadj_sup a ha
  · intro a ha
    have hne : A x ≠ A a := fun h => ((hAdj x a).mp ha).1 (hA h)
    exact (op1370_two_rank_strict_subset k (A x) (A a)
      (levels x) (levels a) (hadj_sup a ha) hne).2.2
