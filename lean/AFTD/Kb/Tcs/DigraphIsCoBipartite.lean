import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsSemicomplete

/-!
# digraph_is_co_bipartite

Topic: graphs   Node: abbd509415a8

Provenance: formalization of a published result. Source: arXiv:2610.36895 Sec. 6

A digraph D is co-bipartite if it is loopless and its vertex set can be partitioned into two disjoint subsets each of which induces a semicomplete subdigraph.
-/

/-- A digraph is co-bipartite if its vertex set can be partitioned into two induced semicomplete subdigraphs. -/
def digraph_is_co_bipartite {V : Type*} (D : Digraph V) : Prop :=
  (∀ v : V, ¬ D.Adj v v) ∧
  ∃ (V₁ V₂ : Set V), (∀ v, v ∈ V₁ ∨ v ∈ V₂) ∧ Disjoint V₁ V₂ ∧
    (∀ u ∈ V₁, ∀ v ∈ V₁, u ≠ v → D.Adj u v ∨ D.Adj v u) ∧
    (∀ u ∈ V₂, ∀ v ∈ V₂, u ≠ v → D.Adj u v ∨ D.Adj v u)
