import AFTD.Prelude
import AFTD.Kb.Tcs.Op309UncoloredAlmostStarForest
import AFTD.Kb.Tcs.Op309PaddedComponentIncidence
import AFTD.Kb.Tcs.Op309CommonHostGraph
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel

/-!
# op309_overlap_selection_pred

Topic: graphs   Node: d81ba412f8d1

Provenance: helper lemma. OP-309 overlap-aware incidence selection, IN-1099.

There is a totally edge-dominating selected almost-star forest with at most one P4, a valid padded component-incidence port map, and an incidence-peeling order using at most four distinct neighbors and five counted incidences.
-/

def op309_overlap_selection_pred{V : Type*} [Fintype V] [DecidableEq V]
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
      op309_incidence_overlap_five_peel I
