import AFTD.Prelude
import AFTD.Kb.Tcs.MonoColorSubgraph

/-!
# bipartite_ramsey_property

Topic: graphs   Node: adea51c3bd27

Provenance: formalization of a published result. Source: arXiv:2610.29813

For a simple graph H and natural numbers r and N, bipartite_ramsey_property H r N holds if every r-edge-colouring of the complete bipartite graph K_{N,N} contains a monochromatic copy of H.
-/

/-- The bipartite Ramsey property br(H; r, N): every r-edge-colouring of K_{N,N} contains a monochromatic copy of H. -/
def bipartite_ramsey_property {α : Type*} (H : SimpleGraph α) (r N : ℕ) : Prop :=
  ∀ c : (completeBipartiteGraph (Fin N) (Fin N)).edgeSet → Fin r,
    ∃ col : Fin r, SimpleGraph.IsContained H (mono_color_subgraph (completeBipartiteGraph (Fin N) (Fin N)) c col)
