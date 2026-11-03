import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOrientedSmallOverlapGoodCenter
import AFTD.Kb.Tcs.DigraphCleanOutneighborhoodCyclePackingStep
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphLocalOutneighborhoodCycle
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_small_overlap_arc_dominated_cycle_packing_step

Topic: graphs   Node: 916a8334ae30

Provenance: helper lemma. General small-overlap cycle-packing induction for OP-110.

The k-cycle theorem at outdegree d implies the (k+1)-cycle theorem for oriented arc-dominated digraphs of minimum outdegree at least d+2 when repeated common-predecessor pair incidences are less than one third of their order.
-/

private instance in478_decadj_digraph_small_overlap_arc_dominated_cycle_packing_step {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_small_overlap_arc_dominated_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (k d : ℕ)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v, d + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hsmall : 3 * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) < Fintype.card α)
    (hpack : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, d ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin k → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ s : Fin (k + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  obtain ⟨v,hclean,hcodom⟩ := digraph_oriented_small_overlap_good_center α D hloop hori hdom hsmall
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
