import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeGraph

/-!
# hypercube_red_subgraph

Topic: combinatorics   Node: a191ec6fca65

Provenance: formalization of a published result. Source: arXiv:2611.16243 Section 2

Given n : ℕ and an edge coloring c : (hypercube_graph n).edgeSet → Bool, hypercube_red_subgraph n c is the simple graph on vertex type Fin n → Bool where vertices u and v are adjacent if and only if there exists a proof h that u and v are adjacent in hypercube_graph n such that c ⟨s(u, v), h⟩ = true.
-/

/-- The spanning subgraph of Q_n formed by the edges of color red (true) under edge coloring c. -/
def hypercube_red_subgraph (n : ℕ) (c : (hypercube_graph n).edgeSet → Bool) : SimpleGraph (Fin n → Bool) where
  Adj u v := ∃ h : (hypercube_graph n).Adj u v, c ⟨s(u, v), h⟩ = true
  symm := ⟨by
    intro u v ⟨h, hc⟩
    refine ⟨h.symm, ?_⟩
    have : (⟨s(v, u), h.symm⟩ : (hypercube_graph n).edgeSet) = ⟨s(u, v), h⟩ := Subtype.ext Sym2.eq_swap
    rw [this]
    exact hc⟩
  loopless := ⟨by
    intro u ⟨h, _⟩
    exact (hypercube_graph n).loopless.irrefl u h⟩
