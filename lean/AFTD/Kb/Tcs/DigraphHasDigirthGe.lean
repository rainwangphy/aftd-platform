import AFTD.Prelude

/-!
# digraph_has_digirth_ge

Topic: graphs   Node: ffb70117868b

Provenance: formalization of a published result. Source: arXiv:2610.38574 Section 2.1

A digraph D has digirth at least g if every directed cycle of length at least 2 in D (represented by a list c of distinct vertices with 2 ≤ c.length that forms a directed chain in D whose last vertex has an arc to its first vertex) has length at least g.
-/

/-- A digraph has digirth at least g if every directed cycle of length at least 2 has length at least g. -/
def digraph_has_digirth_ge {V : Type*} (D : Digraph V) (g : ℕ) : Prop := ∀ c : List V, (c.Nodup ∧ 2 ≤ c.length ∧ c.IsChain D.Adj ∧
    ∃ u v, c.head? = some u ∧ c.getLast? = some v ∧ D.Adj v u) → g ≤ c.length
