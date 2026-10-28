import AFTD.Prelude

/-!
# has_mad_lt

Topic: graphs   Node: dd3a901b7cbb

Provenance: formalization of a published result. Source: arXiv:2610.34874

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and a rational number q, has_mad_lt G q asserts that for every nonempty finite subset s of V, twice the number of edges in the induced subgraph of G on s divided by the cardinality of s (evaluated in ℚ) is strictly less than q.
-/

/-- The maximum average degree of G is strictly less than a rational number q. -/
def has_mad_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℚ) : Prop := ∀ (s : Finset V) (_ : s.Nonempty),
    2 * ((G.induce (s : Set V)).edgeFinset.card : ℚ) / (s.card : ℚ) < q
