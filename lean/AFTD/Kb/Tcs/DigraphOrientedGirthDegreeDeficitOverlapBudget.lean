import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.GirthChargeMultiplicityBound
import AFTD.Kb.Tcs.DigraphShortParentSetNotAllCharged
import AFTD.Kb.Tcs.FiniteEndomapLocalDegreeDeficitLeMissingImage
import AFTD.Kb.Tcs.DigraphGirthArcMapMissingBudget

/-!
# digraph_oriented_girth_degree_deficit_overlap_budget

Topic: graphs   Node: 9d61135d5b73

Provenance: helper lemma. Girth-dependent collision accounting for the four-cycle campaign; experiment 13463.

In a finite loopless oriented arc-dominated digraph whose directed cycles have at least g vertices, with g at least three, g−1 times the sum of positive outdegree-minus-indegree deficits is at most g times the repeated common-predecessor incidence count.
-/

private instance in516_girth_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_oriented_girth_degree_deficit_overlap_budget
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (g : ℕ) (hg : 3 ≤ g) (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdom : ∀ u v, D.Adj u v → ∃ p, D.Adj p u ∧ D.Adj p v)
    (hgirth : ∀ C : Finset α, digraph_directed_cycle_on D C → g ≤ C.card) :
    (g - 1) * (∑ v : α, ((Finset.univ.filter fun w => D.Adj v w).card -
      (Finset.univ.filter fun w => D.Adj w v).card)) ≤
      g * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
        (digraph_common_predecessor_graph D).edgeFinset.card) := by
  classical
  let choose : α → α → α := fun u v => if h : D.Adj u v then Classical.choose (hdom u v h) else u
  have hchoice : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v := by
    intro u v h
    simpa [choose, h] using Classical.choose_spec (hdom u v h)
  let Arc := {e : α × α // D.Adj e.1 e.2}
  let f : Arc → Arc := fun e => ⟨(choose e.val.1 e.val.2,e.val.1), (hchoice _ _ e.property).1⟩
  let r : Arc → Arc := fun y => if h : ∃ x, f x = y then Classical.choose h else y
  have hr : ∀ x, f (r (f x)) = f x := by
    intro x
    dsimp [r]
    split
    · rename_i h
      exact Classical.choose_spec h
    · rename_i h
      exact (h ⟨x,rfl⟩).elim
  let tail : Arc → α := fun e => e.val.1
  let head : Arc → α := fun e => e.val.2
  have hf : ∀ e, head (f e) = tail e := by intro e; rfl
  have hout (v : α) : (Finset.univ.filter fun e : Arc => tail e = v).card =
      (Finset.univ.filter fun w => D.Adj v w).card := by
    apply Finset.card_bij (fun e _ => e.val.2)
    · intro e he
      have ht : e.val.1 = v := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [ht] using e.property⟩
    · intro e he e' he' hh
      apply Subtype.ext
      apply Prod.ext
      · have h1 : e.val.1 = v := (Finset.mem_filter.mp he).2
        have h2 : e'.val.1 = v := (Finset.mem_filter.mp he').2
        exact h1.trans h2.symm
      · exact hh
    · intro w hw
      have ha : D.Adj v w := (Finset.mem_filter.mp hw).2
      refine ⟨⟨(v,w),ha⟩, ?_, rfl⟩
      simp [tail]
  have hin (v : α) : (Finset.univ.filter fun e : Arc => head e = v).card =
      (Finset.univ.filter fun w => D.Adj w v).card := by
    apply Finset.card_bij (fun e _ => e.val.1)
    · intro e he
      have ht : e.val.2 = v := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [ht] using e.property⟩
    · intro e he e' he' hh
      apply Subtype.ext
      apply Prod.ext
      · exact hh
      · have h1 : e.val.2 = v := (Finset.mem_filter.mp he).2
        have h2 : e'.val.2 = v := (Finset.mem_filter.mp he').2
        exact h1.trans h2.symm
    · intro w hw
      have ha : D.Adj w v := (Finset.mem_filter.mp hw).2
      refine ⟨⟨(w,v),ha⟩, ?_, rfl⟩
      simp [head]
  have hfinite := finite_endomap_local_degree_deficit_le_missing_image Arc α f r tail head hr hf
  have hsum : (∑ v : α, ((Finset.univ.filter fun w => D.Adj v w).card -
      (Finset.univ.filter fun w => D.Adj w v).card)) ≤
      ((Finset.univ : Finset Arc) \ Finset.univ.image f).card := by
    simpa only [hout,hin] using hfinite
  have hbudget := digraph_girth_arc_map_missing_budget α D choose g hg hgirth hloop hori hchoice
  change (g - 1) * ((Finset.univ : Finset Arc) \ Finset.univ.image f).card ≤ _ at hbudget
  exact (Nat.mul_le_mul_left (g - 1) hsum).trans hbudget
