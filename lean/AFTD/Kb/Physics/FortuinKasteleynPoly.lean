import AFTD.Prelude

/-!
# fortuin_kasteleyn_poly

Topic: quantum_mechanics   Node: 0afd16b1ac5c

Provenance: formalization of a published result. Source: OP-1695; Fortuin-Kasteleyn (1972)

For a finite simple graph G = (V, E) and real parameters q, w, the Fortuin-Kasteleyn random-cluster polynomial Z_G(q, w) is the sum over all edge subsets A ⊆ E of w^{|A|} q^{k(V, A)}, where k(V, A) is the number of connected components of the spanning subgraph (V, A).
-/

open scoped Classical in
/-- The Fortuin-Kasteleyn random-cluster polynomial Z_G(q, w) = ∑_{A ⊆ E} w^{|A|} q^{k(V, A)}. -/
noncomputable def fortuin_kasteleyn_poly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q w : ℝ) : ℝ := ∑ A ∈ G.edgeFinset.powerset,
    (w ^ A.card) * q ^ (Fintype.card (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).ConnectedComponent)
