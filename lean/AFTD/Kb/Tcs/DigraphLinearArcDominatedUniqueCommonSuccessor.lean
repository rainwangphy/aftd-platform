import AFTD.Prelude

/-!
# digraph_linear_arc_dominated_unique_common_successor

Topic: graphs   Node: 574f1b0deae7

Provenance: helper lemma. General zero-overlap duality route for OP-110; exhaustive small checks in experiment 12675.

Every arc of a finite loopless linear arc-dominated digraph has exactly one common successor; regularity and orientation are not required.
-/

theorem digraph_linear_arc_dominated_unique_common_successor
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hlinear : ∀ u v, u ≠ v → ∀ a b,
      D.Adj a u → D.Adj a v → D.Adj b u → D.Adj b v → a = b)
    (u v : α) (huv : D.Adj u v) :
    ∃! w, D.Adj u w ∧ D.Adj v w := by
  classical
  let Arc := {e : α × α // D.Adj e.1 e.2}
  let pred : Arc → α := fun e => Classical.choose (hdom e.val.1 e.val.2 e.property)
  have hpred : ∀ e : Arc, D.Adj (pred e) e.val.1 ∧ D.Adj (pred e) e.val.2 := by
    intro e
    exact Classical.choose_spec (hdom e.val.1 e.val.2 e.property)
  let f : Arc → Arc := fun e => ⟨(pred e, e.val.1), (hpred e).1⟩
  have hinj : Function.Injective f := by
    intro e k h
    have hp : pred e = pred k := congrArg (fun z : Arc => z.val.1) h
    have ht : e.val.1 = k.val.1 := congrArg (fun z : Arc => z.val.2) h
    apply Subtype.ext
    apply Prod.ext
    · exact ht
    · by_contra hne
      have hk : D.Adj e.val.1 k.val.2 := by simpa [ht] using k.property
      have hpk : D.Adj (pred e) k.val.2 := by simpa [hp] using (hpred k).2
      have heq : e.val.1 = pred e :=
        hlinear e.val.2 k.val.2 hne e.val.1 (pred e)
          e.property hk (hpred e).2 hpk
      exact hloop e.val.1 (by simpa [← heq] using (hpred e).1)
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  obtain ⟨e, he⟩ := hsurj ⟨(u, v), huv⟩
  have hp : pred e = u := congrArg (fun z : Arc => z.val.1) he
  have ht : e.val.1 = v := congrArg (fun z : Arc => z.val.2) he
  have h1 : D.Adj u e.val.2 := by simpa [hp] using (hpred e).2
  have h2 : D.Adj v e.val.2 := by simpa [ht] using e.property
  refine ⟨e.val.2, ⟨h1, h2⟩, ?_⟩
  intro w hw
  by_contra hne
  have heq : u = v := hlinear w e.val.2 hne u v hw.1 h1 hw.2 h2
  exact hloop u (by simpa [← heq] using huv)
