import AFTD.Prelude
import AFTD.Kb.Tcs.IsGoodSetForEdge

/-!
# is_type_ii_edge

Topic: graphs   Node: 6ac10f4f6c29

Provenance: formalization of a published result. Source: arXiv:2611.09072, Lemma 2.8(ii)

An edge uv of a simple graph G is a type II edge with parameter k if u is adjacent to v, there exists a good set S for uv of cardinality k + 1, every good set for uv has cardinality at least k + 1, and for every good set S of cardinality k + 1, the graph (G - uv)[Sᶜ] has exactly 3 connected components, and the connected components containing u and v have supports equal to the singletons {u} and {v} respectively.
-/

/-- An edge uv in G is a type II edge with parameter k if G.Adj u v, the minimum cardinality of any good set is k + 1, and every good set of cardinality k + 1 separates G - uv into 3 components, two being singletons {u} and {v}. -/
def is_type_ii_edge {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) (k : ℕ) : Prop := G.Adj u v ∧
  (∃ S : Finset V, is_good_set_for_edge G u v S k ∧ S.card = k + 1) ∧
  (∀ S : Finset V, is_good_set_for_edge G u v S k → k + 1 ≤ S.card) ∧
  (∀ S : Finset V, is_good_set_for_edge G u v S k → S.card = k + 1 →
    ∃ (hu : u ∉ S) (hv : v ∉ S),
      let H := (G.deleteEdges {s(u, v)}).induce (S : Set V)ᶜ
      Nat.card H.ConnectedComponent = 3 ∧
      (H.connectedComponentMk ⟨u, hu⟩).supp = {⟨u, hu⟩} ∧
      (H.connectedComponentMk ⟨v, hv⟩).supp = {⟨v, hv⟩})
