import AFTD.Prelude

/-!
# matroid_strongly_base_orderable

Topic: combinatorics   Node: 2c45d1975a3f

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Sec. 1.3 (definition of strong base orderability)

A matroid M is strongly base-orderable if for every two bases B₁, B₂ there is a bijection φ : B₁ → B₂ such that (B₁ \ X) ∪ φ(X) is a base for every X ⊆ B₁.
-/

/-- A matroid is strongly base-orderable if for every two bases `B₁`, `B₂` there is a bijection `φ : B₁ → B₂` such that exchanging any subset `X ⊆ B₁` for its image gives a base: `(B₁ \ X) ∪ φ(X)` is a base for every `X ⊆ B₁`. -/
def matroid_strongly_base_orderable {α : Type*} (M : Matroid α) : Prop :=
  ∀ B₁ B₂ : Set α, M.IsBase B₁ → M.IsBase B₂ →
    ∃ φ : B₁ ≃ B₂, ∀ X : Set B₁,
      M.IsBase ((B₁ \ ((↑) '' X)) ∪ ((fun x => (φ x : α)) '' X))
