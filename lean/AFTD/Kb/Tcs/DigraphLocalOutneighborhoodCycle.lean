import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphFinitePredecessorClosedSetCycle

/-!
# digraph_local_outneighborhood_cycle

Topic: graphs   Node: 9696539269ee

Provenance: helper lemma. Local-cycle helper for the small-overlap structural route to OP-110.

If an out-neighborhood is nonempty and each of its vertices has an out-neighbor inside it, it contains a directed cycle.
-/

private theorem in504_reverse_cycle (α : Type) [DecidableEq α]
    (D : Digraph α) (C : Finset α)
    (h : digraph_directed_cycle_on ⟨fun u v => D.Adj v u⟩ C) :
    digraph_directed_cycle_on D C := by
  obtain ⟨l, hnodup, hlen, hset, hchain, a, b, ha, hb, hab⟩ := h
  refine ⟨l.reverse, ?_, ?_, ?_, ?_, b, a, ?_, ?_, ?_⟩
  · exact List.nodup_reverse.mpr hnodup
  · simpa using hlen
  · simpa using hset
  · exact List.isChain_reverse.mpr hchain
  · simpa using hb
  · simpa using ha
  · exact hab

theorem digraph_local_outneighborhood_cycle
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (v : α) (hv : ∃ w, D.Adj v w)
    (hcodom : ∀ w, D.Adj v w → ∃ x, D.Adj v x ∧ D.Adj w x) :
    ∃ C : Finset α, digraph_directed_cycle_on D C ∧ ∀ w ∈ C, D.Adj v w := by
  classical
  let R : Digraph α := ⟨fun u w => D.Adj w u⟩
  let T : Finset α := Finset.univ.filter fun w => D.Adj v w
  have hT : T.Nonempty := by
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, by simp [T, hw]⟩
  have hpred : ∀ w ∈ T, ∃ x ∈ T, R.Adj x w := by
    intro w hw
    have h₁ : D.Adj v w := (Finset.mem_filter.mp hw).2
    obtain ⟨x, hvx, hwx⟩ := hcodom w h₁
    exact ⟨x, by simp [T, hvx], hwx⟩
  obtain ⟨C, hC, hsub⟩ := digraph_finite_predecessor_closed_set_cycle α R T hT hloop hpred
  refine ⟨C, in504_reverse_cycle α D C hC, ?_⟩
  intro w hw
  exact (Finset.mem_filter.mp (hsub hw)).2
