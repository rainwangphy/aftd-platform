import AFTD.Prelude

/-!
# one_weight_level

Topic: combinatorics   Node: af02165a75c2

Provenance: formalization of a published result. Source: arXiv:2611.22205 Section 2

For an arbitrary finite type ι, integer weights ω : α → ℤ, and a word w : ι → α, one_weight_level ω w is the sum over all i : ι of ω (w i) in ℤ.
-/

/-- The one-weight level of a word with given coordinate weights. -/
def one_weight_level {α ι : Type*} [Fintype ι] (ω : α → ℤ) (w : ι → α) : ℤ := ∑ i, ω (w i)
