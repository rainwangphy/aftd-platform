import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGirthCorrection
import AFTD.Kb.Tcs.DigraphGirthArcMapWeightedBudget
import AFTD.Kb.Tcs.DigraphGoodCenterFromArcMapBudget

/-!
# digraph_girth_weighted_good_center

Topic: graphs   Node: 2296fbbaef44

Provenance: helper lemma. Weighted center route for the four-cycle campaign; experiment 13473.

Under the displayed weighted overlap condition, a finite loopless oriented arc-dominated digraph of the specified girth has a clean out-neighborhood whose outgoing arcs each have a common successor.
-/

private instance in516_girth_center_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_girth_weighted_good_center
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (g : ℕ) (hg : 3 ≤ g) (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hgirth : ∀ C : Finset α, digraph_directed_cycle_on D C → g ≤ C.card)
    (hdom : ∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v)
    (hsmall : 2 * g * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) + digraph_common_predecessor_girth_correction α D g < (g - 1) * Fintype.card α) :
    ∃ v, (∀ a b, a ≠ b → D.Adj v a → D.Adj v b →
        ∀ p, D.Adj p a → D.Adj p b → p = v) ∧
      (∀ w, D.Adj v w → ∃ x, D.Adj v x ∧ D.Adj w x) := by
  classical
  let choose : α → α → α := fun u v => if h : D.Adj u v then Classical.choose (hdom u v h) else u
  have hchoice : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v := by
    intro u v h
    simpa [choose,h] using Classical.choose_spec (hdom u v h)
  let Arc := {e : α × α // D.Adj e.1 e.2}
  let f : Arc → Arc := fun e => ⟨(choose e.val.1 e.val.2,e.val.1),(hchoice _ _ e.property).1⟩
  let dirty : Finset α := Finset.univ.filter fun u =>
    ∃ a b p, a ≠ b ∧ p ≠ u ∧ D.Adj u a ∧ D.Adj u b ∧ D.Adj p a ∧ D.Adj p b
  let missing : Finset Arc := Finset.univ \ Finset.univ.image f
  have hw := digraph_girth_arc_map_weighted_budget α D choose g hg hloop hori hgirth hchoice
  have hb : dirty.card + missing.card < Fintype.card α := by
    change (g - 1) * (dirty.card + missing.card) ≤ _ at hw
    have hlt : (g - 1) * (dirty.card + missing.card) < (g - 1) * Fintype.card α := lt_of_le_of_lt hw hsmall
    exact Nat.lt_of_mul_lt_mul_left hlt
  exact digraph_good_center_from_arc_map_budget α D choose hchoice hb
