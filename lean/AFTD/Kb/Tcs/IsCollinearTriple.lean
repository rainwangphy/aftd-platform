import AFTD.Prelude

/-!
# IsCollinearTriple

Topic: graphs   Node: 228e154c3633

Provenance: formalization of a published result. Source: arXiv:2610.39966 Section 2

A set T of vertices in a simple graph G is collinear if there exist three pairwise distinct vertices x, y, z in T such that G.dist x y + G.dist y z = G.dist x z.
-/

/-- Collinear triple predicate on a vertex set of a simple graph. -/
def IsCollinearTriple {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ∃ x y z, x ∈ T ∧ y ∈ T ∧ z ∈ T ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.dist x y + G.dist y z = G.dist x z
