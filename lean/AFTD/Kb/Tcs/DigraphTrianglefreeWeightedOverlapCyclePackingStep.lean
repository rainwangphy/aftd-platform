import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorDoubleEdges
import AFTD.Kb.Tcs.DigraphTrianglefreeArcMapWeightedBudget
import AFTD.Kb.Tcs.DigraphGoodCenterFromArcMapBudget
import AFTD.Kb.Tcs.DigraphLocalOutneighborhoodCycle
import AFTD.Kb.Tcs.DigraphCleanOutneighborhoodCyclePackingStep
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphTrianglefreeWeightedGoodCenter

/-!
# digraph_trianglefree_weighted_overlap_cycle_packing_step

Topic: graphs   Node: 622354ec7fba

Provenance: helper lemma. Triangle-free center budget for the four-cycle campaign; experiments 13471 and 13473.

For a loopless oriented arc-dominated digraph of directed girth at least four, the k-cycle theorem at outdegree d implies a (k+1)-cycle packing at outdegree d+2 whenever eight times the repeated-pair incidence count plus the number of multiplicity-two pairs is less than three times the order.
-/

private instance in516_weighted_pack_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_trianglefree_weighted_overlap_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (k d : ℕ)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hgirth : ∀ C : Finset α, digraph_directed_cycle_on D C → 4 ≤ C.card)
    (hdeg : ∀ v, d + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hdom : ∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v)
    (hsmall : 8 * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) +
      digraph_common_predecessor_double_edges α D < 3 * Fintype.card α)
    (hpack : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, d ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin k → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ s : Fin (k + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  obtain ⟨v,hclean,hcodom⟩ := digraph_trianglefree_weighted_good_center α D hloop hori hgirth hdom hsmall
  have hv : ∃ w, D.Adj v w := by
    have hp : 0 < (Finset.univ.filter fun w => D.Adj v w).card := by
      have := hdeg v
      omega
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hp
    exact ⟨w,(Finset.mem_filter.mp hw).2⟩
  obtain ⟨C,hC,hCout⟩ := digraph_local_outneighborhood_cycle α D hloop v hv hcodom
  obtain ⟨w,hw⟩ := hv
  obtain ⟨p,hpv,_⟩ := hdom v w hw
  exact digraph_clean_outneighborhood_cycle_packing_step α D k d hloop hori hdeg hpack
    v C hC hCout hclean p hpv
