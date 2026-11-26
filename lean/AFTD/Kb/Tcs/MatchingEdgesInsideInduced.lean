import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# matching_edges_inside_induced

Topic: graphs   Node: bcf6f36381cc

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

The edges of a matching supported in a set and contained in a subgraph are contained in the induced edge set.
-/

theorem matching_edges_inside_induced
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M P : G.Subgraph) (hMP : M ≤ P) (S : Finset V) (hMS : M.verts ⊆ (S : Set V)) :
    M.edgeSet ⊆ (P.induce (S : Set V)).edgeSet := by
  set_option maxHeartbeats 4000000 in
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : M.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp he
      change u ∈ (S : Set V) ∧ v ∈ (S : Set V) ∧ P.Adj u v
      exact ⟨hMS (M.edge_vert huv), hMS (M.edge_vert huv.symm), hMP.2 huv⟩
