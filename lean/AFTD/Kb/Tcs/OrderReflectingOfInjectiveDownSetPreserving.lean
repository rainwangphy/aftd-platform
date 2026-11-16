import AFTD.Prelude

/-!
# order_reflecting_of_injective_down_set_preserving

Topic: combinatorics   Node: 3ecc63d39d8f

Provenance: helper lemma. arXiv:2611.15540, Lemma 3.1: Solutions of the set-theoretic quantum Yang-Baxter equation arising from posets

If a map α : P → Q between preordered types is injective and preserves principal down-sets (that is, the image of Set.Iic x under α is Set.Iic (α x) for all x in P), then α preserves and reflects the order: α x ≤ α y ↔ x ≤ y for all x, y in P.
-/

/-- An injective map between preordered types preserving principal down-sets is order-reflecting and order-preserving. -/
theorem order_reflecting_of_injective_down_set_preserving
    {P Q : Type*} [Preorder P] [Preorder Q] (α : P → Q) (hα : Function.Injective α)
    (h_down : ∀ x : P, α '' Set.Iic x = Set.Iic (α x)) (x y : P) :
    α x ≤ α y ↔ x ≤ y := by
  constructor
  · intro h
    have hmem : α x ∈ α '' Set.Iic y := by
      rw [h_down y]
      exact h
    rcases hmem with ⟨z, hz, hzx⟩
    have : z = x := hα hzx
    simpa [this] using hz
  · intro h
    have hmem : x ∈ Set.Iic y := h
    have : α x ∈ α '' Set.Iic y := ⟨x, hmem, rfl⟩
    rwa [h_down y] at this
