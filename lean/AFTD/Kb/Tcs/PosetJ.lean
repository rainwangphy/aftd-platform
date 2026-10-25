import AFTD.Prelude

/-!
# poset_j

Topic: combinatorics   Node: e82baa9bc73f

Provenance: helper lemma. step towards op314_poset_tower_two_cancellation

For a partial order α, the subposet J(α) of elements having exactly one lower cover (exactly one element c with c ⋖ x).
-/

/-- The subposet of elements with exactly one lower cover; the set J(X) of the A^A reconstruction proof (arXiv:2610.20802, Section 2.3). -/
abbrev poset_j (α : Type*) [PartialOrder α] : Type _ := {x : α // ∃! c : α, c ⋖ x}
