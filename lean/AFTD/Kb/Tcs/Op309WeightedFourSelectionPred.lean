import AFTD.Prelude
import AFTD.Kb.Tcs.Op309UncoloredAlmostStarForest
import AFTD.Kb.Tcs.Op309PaddedComponentIncidence
import AFTD.Kb.Tcs.Op309CommonHostGraph
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid
import AFTD.Kb.Tcs.Op309IncidenceWeightedFourPeel

/-!
# op309_weighted_four_selection_pred

Topic: graphs   Node: 4d5a099574ad

Provenance: helper lemma. OP-309 weighted-four shortcut examined in IN-1099.

A dominating padded almost-star port system with at most one P4 whose class-host incidence system has weighted-four peeling.
-/

def op309_weighted_four_selection_pred{V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ R : Finset G.edgeSet,
    op309_uncolored_almost_star_forest G R ∧
    (∀ e : G.edgeSet, (∃ f, G.lineGraph.Adj e f) →
      ∃ f ∈ R, G.lineGraph.Adj e f) ∧
    (∀ e ∈ R, ∀ f ∈ R,
      (∃ a b : V, e.1 = s(a,b) ∧
        (R.filter fun g => a ∈ g.1).card = 2 ∧
        (R.filter fun g => b ∈ g.1).card = 2) →
      (∃ a b : V, f.1 = s(a,b) ∧
        (R.filter fun g => a ∈ g.1).card = 2 ∧
        (R.filter fun g => b ∈ g.1).card = 2) → e = f) ∧
    ∃ (n m : ℕ) (q : Sum G.edgeSet (V × Fin 3) → Fin n)
      (host : V → Fin m) (I : SimpleGraph (Fin n ⊕ Fin m))
      (inst : DecidableRel I.Adj),
      letI : DecidableRel I.Adj := inst
      op309_padded_component_incidence G R q host I ∧
      op309_padded_almost_star_port_graph_valid G R (op309_common_host_graph I) q ∧
      op309_incidence_weighted_four_peel I
