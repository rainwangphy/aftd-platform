import AFTD.Prelude

/-!
# is_connected_poset

Topic: combinatorics   Node: 306d4751906a

Provenance: formalization of a published result. Source: arXiv:2611.15540, Section 3

A partially ordered set P is connected if every pair of elements is related by the reflexive-transitive closure of comparability.
-/

/-- A poset is connected if its comparability relation's reflexive-transitive closure relates every pair of elements. -/
def is_connected_poset (P : Type*) [PartialOrder P] : Prop :=
  ∀ x y : P, Relation.ReflTransGen (fun a b => a ≤ b ∨ b ≤ a) x y
