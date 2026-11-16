import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeGraph
import AFTD.Kb.Tcs.HypercubeAntipode

/-!
# is_antipodal_coloring

Topic: combinatorics   Node: 1a6b585d7bac

Provenance: formalization of a published result. Source: arXiv:2611.16243 Section 1

Given n : ℕ, an edge coloring c : (hypercube_graph n).edgeSet → Bool is antipodal if for all vertices u, v : Fin n → Bool, given proofs h that u and v are adjacent in hypercube_graph n and h' that their antipodal vertices hypercube_antipode u and hypercube_antipode v are adjacent, c ⟨s(u, v), h⟩ = !c ⟨s(hypercube_antipode u, hypercube_antipode v), h'⟩.
-/

/-- An edge coloring of Q_n is antipodal if every edge has the opposite color to its antipodal edge. -/
def is_antipodal_coloring (n : ℕ) (c : (hypercube_graph n).edgeSet → Bool) : Prop := ∀ (u v : Fin n → Bool) (h : (hypercube_graph n).Adj u v)
  (h' : (hypercube_graph n).Adj (hypercube_antipode u) (hypercube_antipode v)),
  c ⟨s(u, v), h⟩ = !c ⟨s(hypercube_antipode u, hypercube_antipode v), h'⟩
