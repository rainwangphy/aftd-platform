import AFTD.Prelude

/-!
# tree_routing_cost

Topic: approximation   Node: 9e1865a93639

Provenance: formalization of a published result. Source: arXiv:2610.39863, Section 3

For any finite type V, type W, simple graph T on V, simple graph H on W, and function f : V → W, tree_routing_cost T H f is the sum over all undirected edges uv of T of the graph distance in H between f(u) and f(v).
-/

/-- The routing cost of a simple graph T on a finite type V in a host graph H under a function f : V → W. -/
noncomputable def tree_routing_cost {V W : Type*} [Fintype V]
    (T : SimpleGraph V) (H : SimpleGraph W) (f : V → W) : ℕ := open Classical in
  ∑ e ∈ T.edgeFinset,
    Sym2.lift ⟨fun u v ↦ H.dist (f u) (f v), fun _ _ ↦ H.dist_comm⟩ e
