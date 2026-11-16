import AFTD.Prelude

/-!
# order_iso_of_bijective_order_reflecting

Topic: combinatorics   Node: 7505f9715556

Provenance: helper lemma. arXiv:2611.15540, Lemma 3.1: Solutions of the set-theoretic quantum Yang-Baxter equation arising from posets

If a map α : P → Q between preordered types is bijective and satisfies α x ≤ α y ↔ x ≤ y for all x, y in P, then there exists an order isomorphism e : P ≃o Q whose underlying function is α.
-/

/-- A bijective order-preserving and order-reflecting map lifts to an order isomorphism. -/
theorem order_iso_of_bijective_order_reflecting
    {P Q : Type*} [Preorder P] [Preorder Q] (α : P → Q) (hα : Function.Bijective α)
    (h_rel : ∀ x y : P, α x ≤ α y ↔ x ≤ y) :
    ∃ e : P ≃o Q, ⇑e = α := by
  refine ⟨RelIso.mk (Equiv.ofBijective α hα) ?_, ?_⟩
  · intro a b
    exact h_rel a b
  · rfl
