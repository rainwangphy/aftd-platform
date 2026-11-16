import AFTD.Prelude
import AFTD.Kb.Tcs.PosetDownSetPreservingBijectiveEq
import AFTD.Kb.Tcs.OrderReflectingOfInjectiveDownSetPreserving

/-!
# poset_rigidity_of_down_set_preserving_bijections

Topic: combinatorics   Node: 4f6aad524c83

Provenance: formalization of a published result. Source: arXiv:2611.15540, Lemma 3.1: Solutions of the set-theoretic quantum Yang-Baxter equation arising from posets

Let P and Q be finite posets, and let α, β : P → Q be bijective maps such that for all x in P, the image under α of the principal down-set Set.Iic x equals the principal down-set Set.Iic (β x). Then α = β, and α is an order isomorphism (for all x, y in P, α x ≤ α y ↔ x ≤ y).
-/

/-- Poset rigidity: down-set preserving bijections are equal and define an order isomorphism. -/
theorem poset_rigidity_of_down_set_preserving_bijections
    {P Q : Type*} [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]
    (α β : P → Q) (hα : Function.Bijective α) (hβ : Function.Bijective β)
    (h_down : ∀ x : P, α '' Set.Iic x = Set.Iic (β x)) :
    α = β ∧ ∀ x y : P, α x ≤ α y ↔ x ≤ y := by
  have hab : α = β := poset_down_set_preserving_bijective_eq α β hα hβ h_down
  refine ⟨hab, ?_⟩
  have h_down' : ∀ x : P, α '' Set.Iic x = Set.Iic (α x) := by
    intro x
    rw [h_down x, hab]
  exact order_reflecting_of_injective_down_set_preserving α hα.injective h_down'
