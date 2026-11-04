import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGirthCorrection
import AFTD.Kb.Tcs.DigraphGirthArcMapWeightedBudget
import AFTD.Kb.Tcs.DigraphGoodCenterFromArcMapBudget
import AFTD.Kb.Tcs.DigraphLocalOutneighborhoodCycle
import AFTD.Kb.Tcs.DigraphCleanOutneighborhoodCyclePackingStep
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphGirthWeightedGoodCenter

/-!
# digraph_girth_weighted_overlap_cycle_packing_step

Topic: graphs   Node: bf3ae9f41a54

Provenance: helper lemma. Girth-dependent center budget for the four-cycle campaign; experiment 13474.

For a loopless oriented arc-dominated digraph of directed girth at least g, the k-cycle theorem at outdegree d implies a (k+1)-cycle packing at outdegree d+2 under the displayed girth-weighted overlap bound.
-/

private instance in516_girth_pack_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_girth_weighted_overlap_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (g k d : ℕ)
    (hg : 3 ≤ g) (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hgirth : ∀ C : Finset α, digraph_directed_cycle_on D C → g ≤ C.card)
    (hdeg : ∀ v, d + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hdom : ∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v)
    (hsmall : 2 * g * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) +
      digraph_common_predecessor_girth_correction α D g < (g - 1) * Fintype.card α)
    (hpack : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, d ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin k → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ s : Fin (k + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  obtain ⟨v, hclean, hcodom⟩ :=
    digraph_girth_weighted_good_center α D g hg hloop hori hgirth hdom hsmall
  have hv : ∃ w, D.Adj v w := by
    have h := hdeg v
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter fun w => D.Adj v w).card by omega)
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  obtain ⟨C, hC, hCout⟩ := digraph_local_outneighborhood_cycle α D hloop v hv hcodom
  obtain ⟨w, hvw⟩ := hv
  obtain ⟨p, hpv, _⟩ := hdom v w hvw
  exact digraph_clean_outneighborhood_cycle_packing_step α D k d hloop hori hdeg hpack v C hC
    hCout hclean p hpv
