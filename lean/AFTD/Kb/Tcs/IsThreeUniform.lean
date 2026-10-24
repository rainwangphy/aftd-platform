import AFTD.Prelude

/-!
# is_three_uniform

Topic: combinatorics   Node: 0d938d01de97

Provenance: formalization of a published result. Source: arXiv:2610.14829 Section 2

A hypergraph F (a finite family of finite sets of vertices) is 3-uniform if every hyperedge e in F has cardinality 3.
-/

/-- A hypergraph F is 3-uniform if every edge has cardinality 3. -/
def is_three_uniform {V : Type*} (F : Finset (Finset V)) : Prop :=
  ∀ e ∈ F, e.card = 3
