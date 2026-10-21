import AFTD.Prelude

/-!
# simple_graph_binding_number

Topic: graphs   Node: 7cea4eceba0d

Provenance: formalization of a published result. Source: arXiv:2610.28536 (A sharp bound on the binding number of K_k-free graphs and the Brandt conjecture), Sec. 1, definition of bind(G)

bind(G) = min{|N_G(S)|/|S| : ∅ ≠ S ⊆ V(G), N_G(S) ≠ V(G)}, where N_G(S) is the union of the neighbourhoods of the vertices of S.
-/

/-- The binding number of a finite graph: the least ratio |N(S)|/|S| over nonempty vertex sets S whose neighbourhood N(S) (the union of the open neighbourhoods of the vertices of S) is not the whole vertex set (0 on the empty vertex type). -/
noncomputable def simple_graph_binding_number {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ S.biUnion (fun v => G.neighborFinset v) ≠ Finset.univ},
    ((S.1.biUnion (fun v => G.neighborFinset v)).card : ℝ) / S.1.card
