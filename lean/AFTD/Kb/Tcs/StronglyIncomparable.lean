import AFTD.Prelude

/-!
# strongly_incomparable

Topic: combinatorics   Node: be18b64db4eb

Provenance: formalization of a published result. Source: arXiv:2611.12199

An indexed family of finset families `𝒜 : ι → Finset (Finset α)` is strongly incomparable if for all `i j : ι` with `i ≠ j`, for all `A ∈ 𝒜 i` and `B ∈ 𝒜 j`, `A` is not a subset of `B`.
-/

/-- Families of sets are strongly incomparable if no set in one family is a subset of a set in another family. -/
def strongly_incomparable {ι α : Type*} (𝒜 : ι → Finset (Finset α)) : Prop := ∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, ¬(A ⊆ B)
