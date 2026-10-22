import AFTD.Prelude

/-!
# IsHereditarySegmentProperty

Topic: online_algorithms   Node: f4b1fa5a4154

Provenance: formalization of a published result. Source: arXiv:2610.23130, Section 1

A predicate P on finite sets of unordered pairs in Sym2 (ℝ × ℝ) is a hereditary segment property if P holds on the empty finset and for all finite sets of unordered pairs s and t in Finset (Sym2 (ℝ × ℝ)), if s ⊆ t and P t holds, then P s holds.
-/

/-- A segment property is hereditary if it holds for the empty set and is closed under taking sub-families. -/
def IsHereditarySegmentProperty (P : Finset (Sym2 (ℝ × ℝ)) → Prop) : Prop := P ∅ ∧ ∀ ⦃s t : Finset (Sym2 (ℝ × ℝ))⦄, s ⊆ t → P t → P s
