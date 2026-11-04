import AFTD.Prelude

/-!
# is_direct_sum_set

Topic: combinatorics   Node: b3d7ab9054dc

Provenance: formalization of a published result. Source: arXiv:2611.05321 Section 1

For subsets A and Z of an additive abelian group G, the sum A + Z is direct if for all a₁, a₂ ∈ A and z₁, z₂ ∈ Z, a₁ + z₁ = a₂ + z₂ implies a₁ = a₂ and z₁ = z₂.
-/

/-- The sum of subsets A and Z in an additive abelian group is direct. -/
def is_direct_sum_set {G : Type*} [AddCommGroup G] (A Z : Set G) : Prop := ∀ a₁ ∈ A, ∀ z₁ ∈ Z, ∀ a₂ ∈ A, ∀ z₂ ∈ Z, a₁ + z₁ = a₂ + z₂ → a₁ = a₂ ∧ z₁ = z₂
