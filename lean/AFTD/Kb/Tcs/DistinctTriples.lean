import AFTD.Prelude

/-!
# distinct_triples

Topic: information   Node: cc37bb274198

Provenance: formalization of a published result. Source: arXiv:2611.21275, Section II

For a finite set s, distinct_triples s is the set of ordered triples (a, b, c) of pairwise distinct elements of s.
-/

/-- The set of ordered triples of pairwise distinct elements in a finite set s. -/
def distinct_triples {α : Type*} [DecidableEq α] (s : Finset α) : Finset (α × α × α) := (s ×ˢ (s ×ˢ s)).filter (fun (a, b, c) => a ≠ b ∧ a ≠ c ∧ b ≠ c)
