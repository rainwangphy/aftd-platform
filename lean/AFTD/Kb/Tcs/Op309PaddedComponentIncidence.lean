import AFTD.Prelude
import AFTD.Kb.Tcs.Op309SelectedEdgeGraph
import AFTD.Kb.Tcs.Op309PaddedBoundaryPort

/-!
# op309_padded_component_incidence

Topic: graphs   Node: 932cd5fe771d

Provenance: helper lemma. OP-309 overlap-aware port incidence selection, IN-1099.

The bipartite relation between port classes and selected-edge components, with private dummy ports only at vertices in selected components.
-/

def op309_padded_component_incidence
    {V A B : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet)
    (q : Sum G.edgeSet (V × Fin 3) → A) (host : V → B)
    (I : SimpleGraph (A ⊕ B)) : Prop :=
  (∀ u v, host u = host v ↔ (op309_selected_edge_graph G R).Reachable u v) ∧
  (∀ a a' : A, ¬ I.Adj (.inl a) (.inl a')) ∧
  (∀ b b' : B, ¬ I.Adj (.inr b) (.inr b')) ∧
  (∀ a : A, ∀ b : B, I.Adj (.inl a) (.inr b) ↔
    ∃ (v : V) (p : Sum G.edgeSet (V × Fin 3)),
      host v = b ∧ q p = a ∧ op309_padded_boundary_port G R v p ∧
      ((R.filter fun e => v ∈ e.1).Nonempty ∨ ∃ e : G.edgeSet, p = .inl e))
