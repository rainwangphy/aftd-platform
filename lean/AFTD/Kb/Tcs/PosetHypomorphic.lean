import AFTD.Prelude

/-!
# poset_hypomorphic

Topic: combinatorics   Node: 510ce7080200

Provenance: formalization of a published result. Source: arXiv:2610.12690 (Reconstruction of Finite Posets of Width Three), Sec. 1–2 (deck of an ordered set, reconstructibility).

Two ordered sets P and Q are hypomorphic (have the same deck) when there is a bijection σ : P → Q such that for every x the one-element-deleted suborder P − x is isomorphic to Q − σ(x); equivalently, the multisets of isomorphism types of one-element deletions coincide.
-/

/-- Two orders are hypomorphic when some bijection `σ` matches every one-element-deleted
suborder `P - x` with an isomorphic one `Q - σ x`: they have the same deck. -/
def poset_hypomorphic (P Q : Type*) [PartialOrder P] [PartialOrder Q] : Prop :=
  ∃ σ : P ≃ Q, ∀ x : P, Nonempty ({y : P // y ≠ x} ≃o {y : Q // y ≠ σ x})
