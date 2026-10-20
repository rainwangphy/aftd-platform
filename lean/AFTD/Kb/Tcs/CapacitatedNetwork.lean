import AFTD.Prelude

/-!
# CapacitatedNetwork

Topic: information   Node: 66b3a4e3a0aa

Provenance: formalization of a published result. Source: arXiv:2610.10108, Sec. 2

An undirected capacitated network on a finite vertex set V given by a simple graph G where each edge in G has strictly positive capacity and non-edges have zero capacity.
-/

/-- An undirected network with positive edge capacities on the edges of a simple graph. -/
structure CapacitatedNetwork (V : Type) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  decAdj : DecidableRel G.Adj
  cap : Sym2 V → ℝ
  cap_pos : ∀ e ∈ G.edgeSet, 0 < cap e
  cap_zero : ∀ e ∉ G.edgeSet, cap e = 0
