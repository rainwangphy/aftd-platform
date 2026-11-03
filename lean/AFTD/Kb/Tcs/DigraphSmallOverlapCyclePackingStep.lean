import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSmallOverlapArcDominatedCyclePackingStep
import AFTD.Kb.Tcs.DigraphDigonCyclePackingStep
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_small_overlap_cycle_packing_step

Topic: graphs   Node: e6523a4919bf

Provenance: helper lemma. General small-overlap cycle-packing induction for OP-110.

The k-cycle theorem at outdegree d implies the (k+1)-cycle theorem for loopless arc-dominated digraphs of minimum outdegree at least d+2 when repeated common-predecessor incidences are fewer than one third of the order.
-/

private instance in478_decadj_digraph_small_overlap_cycle_packing_step {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_small_overlap_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (k d : ℕ)
    (hloop : ∀ v, ¬ D.Adj v v)
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
  by_cases h : ∃ u v, D.Adj u v ∧ D.Adj v u
  · obtain ⟨u,v,huv,hvu⟩ := h
    exact digraph_digon_cycle_packing_step α D k d hloop hdeg hpack u v huv hvu
  · have hori : ∀ u v, D.Adj u v → ¬ D.Adj v u := by
      intro u v huv hvu
      exact h ⟨u,v,huv,hvu⟩
    exact digraph_small_overlap_arc_dominated_cycle_packing_step α D k d hloop hori hdeg hdom hsmall hpack
