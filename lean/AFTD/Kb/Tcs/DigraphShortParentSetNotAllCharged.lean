import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphFinitePredecessorClosedSetCycle

/-!
# digraph_short_parent_set_not_all_charged

Topic: graphs   Node: 586da311e131

Provenance: helper lemma. Girth-dependent collision accounting for the four-cycle campaign; experiment 13463.

In a loopless digraph of directed girth at least g, a nonempty common-predecessor set with fewer than g members cannot have every parent choose the same predecessor for both outgoing arcs.
-/

theorem digraph_short_parent_set_not_all_charged
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (choose : α → α → α) (g : ℕ) (a b : α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hchoice : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v)
    (hgirth : ∀ C : Finset α, digraph_directed_cycle_on D C → g ≤ C.card)
    (hne : (Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b).Nonempty)
    (hsmall : (Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b).card < g) :
    ((Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b).filter
      fun p => choose p a = choose p b).card <
        (Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b).card := by
  classical
  let P : Finset α := Finset.univ.filter fun p => D.Adj p a ∧ D.Adj p b
  let C : Finset α := P.filter fun p => choose p a = choose p b
  have hsub : C ⊆ P := Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  change C.card < P.card
  by_contra hn
  have heq : C = P := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hpred : ∀ u ∈ P, ∃ v ∈ P, D.Adj v u := by
    intro u hu
    have huC : u ∈ C := by rw [heq]; exact hu
    have hsame : choose u a = choose u b := (Finset.mem_filter.mp huC).2
    have huab : D.Adj u a ∧ D.Adj u b := (Finset.mem_filter.mp hu).2
    have ha := hchoice u a huab.1
    have hb := hchoice u b huab.2
    refine ⟨choose u a, ?_, ha.1⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ha.2, by simpa [hsame] using hb.2⟩
  obtain ⟨K,hK,hKP⟩ := digraph_finite_predecessor_closed_set_cycle α D P hne hloop hpred
  have hc := hgirth K hK
  have hle := Finset.card_le_card hKP
  change P.card < g at hsmall
  omega
