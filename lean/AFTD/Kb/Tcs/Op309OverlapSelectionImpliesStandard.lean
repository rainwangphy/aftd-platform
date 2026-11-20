import AFTD.Prelude
import AFTD.Kb.Tcs.Op309OverlapSelectionPred
import AFTD.Kb.Tcs.Op309GraphFourDegenerate
import AFTD.Kb.Tcs.Op309UncoloredAlmostStarForest
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel
import AFTD.Kb.Tcs.Op309CommonHostGraph
import AFTD.Kb.Tcs.Op309PaddedComponentIncidence

/-!
# op309_overlap_selection_implies_standard

Topic: graphs   Node: dfc3acbbbc9c

Provenance: helper lemma. OP-309 overlap-aware incidence selection, IN-1099.

An overlap-aware selection gives the previously stated four-degenerate padded-port selection.
-/

theorem op309_overlap_selection_implies_standard{V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsel : op309_overlap_selection_pred G) :
    ∃ R : Finset G.edgeSet,
      op309_uncolored_almost_star_forest G R ∧
      (∀ e : G.edgeSet, (∃ f, G.lineGraph.Adj e f) → ∃ f ∈ R, G.lineGraph.Adj e f) ∧
      (∀ e ∈ R, ∀ f ∈ R,
        (∃ a b : V, e.1 = s(a,b) ∧ (R.filter fun g => a ∈ g.1).card = 2 ∧
          (R.filter fun g => b ∈ g.1).card = 2) →
        (∃ a b : V, f.1 = s(a,b) ∧ (R.filter fun g => a ∈ g.1).card = 2 ∧
          (R.filter fun g => b ∈ g.1).card = 2) → e = f) ∧
      ∃ (n : ℕ) (Q : SimpleGraph (Fin n)) (q : Sum G.edgeSet (V × Fin 3) → Fin n),
        op309_padded_almost_star_port_graph_valid G R Q q ∧ op309_graph_four_degenerate Q := by
  obtain ⟨R,hf,hd,hone,n,m,q,host,I,inst,hinc,hvalid,hpeel⟩ := hsel
  letI : DecidableRel I.Adj := inst
  refine ⟨R,hf,hd,hone,n,op309_common_host_graph I,q,hvalid,?_⟩
  intro S hS
  obtain ⟨a,ha,hcount,_⟩ := hpeel S hS
  refine ⟨a,ha,S.filter (fun a' => a' ≠ a ∧ ∃ b : Fin m,
    I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b)),?_,?_⟩
  · convert hcount using 1
    congr 1
    ext x
    simp only [Finset.mem_filter]
  · intro a' ha' hadj
    exact Finset.mem_filter.mpr ⟨ha',hadj.1.symm,hadj.2⟩
