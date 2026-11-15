import AFTD.Prelude

/-!
# is_oriented_star

Topic: combinatorics   Node: fade45b5d2bf

Provenance: formalization of a published result. Source: arXiv:2611.15027, Section 6.1

A directed graph D is an oriented star with center c if it is loopless, asymmetric, every edge has c as an endpoint, and every other vertex is adjacent to c in one direction.
-/

/-- A digraph D is an oriented star with center c if every edge is incident to c, there are no loops or antiparallel edges, and every other vertex is adjacent to c. -/
def is_oriented_star {V : Type*} (D : Digraph V) (c : V) : Prop := (∀ v, ¬ D.Adj v v) ∧ (∀ u v, D.Adj u v → u = c ∨ v = c) ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧ (∀ u, u ≠ c → (D.Adj c u ∨ D.Adj u c))
