import AFTD.Prelude

/-!
# graph_interval

Topic: graphs   Node: 90a74b757f13

Provenance: formalization of a published result. Source: arXiv:2610.39966 Section 1

The interval between two vertices u and v in a finite graph G is the finset (Finset V) of all vertices w such that d(u,w) + d(w,v) = d(u,v).
-/

open scoped Classical in
/-- The interval between two vertices u and v in a finite graph G as a finset. -/
noncomputable def graph_interval {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : Finset V := Finset.univ.filter (fun w => G.dist u w + G.dist w v = G.dist u v)
