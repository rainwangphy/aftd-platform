import AFTD.Prelude

/-!
# is_uncomplemented

Topic: combinatorics   Node: a3eb85196aa0

Provenance: formalization of a published result. Source: arXiv:2611.12199

A family of subsets of a finite set is uncomplemented if no set and its complement both belong to the family.
-/

/-- A family of sets is uncomplemented if it contains no set together with its complement. -/
def is_uncomplemented {α : Type*} [Fintype α] [DecidableEq α] (𝒜 : Finset (Finset α)) : Prop := ∀ A ∈ 𝒜, Aᶜ ∉ 𝒜
