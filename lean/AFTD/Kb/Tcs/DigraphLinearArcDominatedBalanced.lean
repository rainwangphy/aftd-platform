import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCleanCenterIndegreeGeOutdegree

/-!
# digraph_linear_arc_dominated_balanced

Topic: graphs   Node: 9e0172aa8931

Provenance: helper lemma. General zero-overlap structure for OP-110; exhaustive checks through order five in experiment 12675.

Every finite loopless linear arc-dominated digraph is balanced, without an outregularity assumption.
-/

theorem digraph_linear_arc_dominated_balanced
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hlinear : ∀ u v, u ≠ v → ∀ a b,
      D.Adj a u → D.Adj a v → D.Adj b u → D.Adj b v → a = b) :
    ∀ v, (Finset.univ.filter fun w => D.Adj v w).card =
      (Finset.univ.filter fun w => D.Adj w v).card := by
  classical
  let outs : α → Finset α := fun v => Finset.univ.filter fun w => D.Adj v w
  let ins : α → Finset α := fun v => Finset.univ.filter fun w => D.Adj w v
  have hle : ∀ v, (outs v).card ≤ (ins v).card := by
    intro v
    apply digraph_clean_center_indegree_ge_outdegree α D hloop hdom v
    intro a b hab hva hvb p hpa hpb
    exact hlinear a b hab p v hpa hpb hva hvb
  have hsum : (∑ v : α, (outs v).card) = ∑ v : α, (ins v).card := by
    calc
      (∑ v : α, (outs v).card) = ∑ v : α, ∑ w : α, if D.Adj v w then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        simp [outs, Finset.sum_ite]
      _ = ∑ w : α, ∑ v : α, if D.Adj v w then 1 else 0 := Finset.sum_comm
      _ = ∑ w : α, (ins w).card := by
        apply Finset.sum_congr rfl
        intro w _
        simp [ins, Finset.sum_ite]
  intro v
  by_contra hne
  have hlt : (outs v).card < (ins v).card := by
    have hv := hle v
    change (outs v).card ≠ (ins v).card at hne
    omega
  have hsumlt : (∑ v : α, (outs v).card) < ∑ v : α, (ins v).card := by
    apply Finset.sum_lt_sum
    · intro w _
      exact hle w
    · exact ⟨v, Finset.mem_univ _, hlt⟩
  omega
