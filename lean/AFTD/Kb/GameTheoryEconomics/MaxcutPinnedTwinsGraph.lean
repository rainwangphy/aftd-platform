import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring

/-!
# maxcut_pinned_twins_graph

Topic: equilibria   Node: 7fee0d06ca84

Provenance: helper lemma. New construction investigated for OP-89, arXiv:2610.04948 Sec. 4 Question 2. Pin anchors are the zeroth twins of the last anchor vertices. Those core-anchor pairs were nonedges in G_3. Sanity check maxcut_pinned_twins_displayed_deviation proves the concrete profitable deviation and initial welfare. All-optimum rigidity is a separate unproved obligation.

A candidate counterexample graph on 182 vertices. Replace each vertex of the paper graph G_3 by two independent twins, replace each old edge by a complete bipartite graph, and join each core twin to the selected padding anchor (j,24,0) for each j different from that core vertex’s initial color.
-/

private instance base_graph_decidable : DecidableRel maxcut_anchor_three_graph.Adj := by
  unfold maxcut_anchor_three_graph
  infer_instance
namespace MaxcutPinnedTwins

private def pin_rel (u v : (Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2) : Prop :=
  match u.1, v.1 with
  | .inl i, .inr (j, a) => a.val = 24 ∧ v.2.val = 0 ∧
      j ≠ maxcut_anchor_three_initial_coloring (.inl i)
  | _, _ => False

private def rel (u v : (Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2) : Prop :=
  maxcut_anchor_three_graph.Adj u.1 v.1 ∨ pin_rel u v

private instance rel_decidable : DecidableRel rel := by
  intro u v
  unfold rel
  haveI : Decidable (pin_rel u v) := by
    rcases u with ⟨u, a⟩
    rcases v with ⟨v, b⟩
    cases u <;> cases v <;> dsimp [pin_rel] <;> infer_instance
  infer_instance

end MaxcutPinnedTwins

def maxcut_pinned_twins_graph : SimpleGraph ((Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2) :=SimpleGraph.fromRel MaxcutPinnedTwins.rel
