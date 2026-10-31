import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountThrough
import AFTD.Kb.Tcs.DigraphArborescenceCount
import AFTD.Kb.Tcs.DigraphArborescenceCountAt
import AFTD.Kb.Tcs.DigraphArborescenceCountAtThrough

/-!
# digraph_arborescence_count_through_sanity

Topic: graphs   Node: 776b0662715c

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

through(D, a → b) vanishes when a → b is not an arc of D, never exceeds tau(D), and on the two-vertex complete digraph the arc 0 → 1 lies in exactly one arborescence.
-/

/-- Sanity checks for the through-arc count: zero on a non-arc, bounded by tau(D), and equal to 1 on the complete digraph on two vertices. -/
theorem digraph_arborescence_count_through_sanity {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj] (a b : Fin n) :
    (a ≠ b → ¬ D.Adj a b → digraph_arborescence_count_through D a b = 0) ∧
    digraph_arborescence_count_through D a b ≤ digraph_arborescence_count D ∧
    @digraph_arborescence_count_through 2 ⊤ (fun _ _ => isTrue trivial) 0 1 = 1 := by
  refine ⟨fun hab hAdj => ?_, ?_, ?_⟩
  · unfold digraph_arborescence_count_through
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [digraph_arborescence_count_at_through, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    rintro ⟨hpr, hout, -, hpab⟩
    obtain rfl | har := eq_or_ne a r
    · rw [hpr] at hpab
      exact hab hpab
    · have := hout a har
      rw [hpab] at this
      exact hAdj this
  · unfold digraph_arborescence_count_through digraph_arborescence_count
    refine Finset.sum_le_sum (fun r _ => ?_)
    rw [digraph_arborescence_count_at_through, digraph_arborescence_count_at]
    refine Finset.card_le_card ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  · decide
