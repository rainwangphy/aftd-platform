import AFTD.Prelude

/-!
# is_good_set_for_edge

Topic: graphs   Node: 2aeafa059886

Provenance: formalization of a published result. Source: arXiv:2611.09072, Section 1

For vertices u and v, a finite subset S disjoint from {u, v} is a good set for the edge uv with parameter k if |S| ≥ k, the number of odd components of (G - uv)[Sᶜ] is |S| - k + 2, and u and v lie in distinct odd connected components of (G - uv)[Sᶜ].
-/

/-- A subset S disjoint from {u,v} is a good set for an edge uv with parameter k if |S| ≥ k, c_o(G - S - uv) = |S| - k + 2, and u and v lie in distinct odd components of G - S - uv. -/
def is_good_set_for_edge {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) (S : Finset V) (k : ℕ) : Prop := u ∉ S ∧ v ∉ S ∧ k ≤ S.card ∧
    ∃ (hu : u ∉ S) (hv : v ∉ S),
      let H := (G.deleteEdges {s(u, v)}).induce (S : Set V)ᶜ
      H.oddComponents.ncard = S.card - k + 2 ∧
      H.connectedComponentMk ⟨u, hu⟩ ∈ H.oddComponents ∧
      H.connectedComponentMk ⟨v, hv⟩ ∈ H.oddComponents ∧
      H.connectedComponentMk ⟨u, hu⟩ ≠ H.connectedComponentMk ⟨v, hv⟩
