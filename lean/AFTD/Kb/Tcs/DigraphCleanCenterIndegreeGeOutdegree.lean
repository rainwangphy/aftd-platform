import AFTD.Prelude

/-!
# digraph_clean_center_indegree_ge_outdegree

Topic: graphs   Node: 9a1a185e4381

Provenance: helper lemma. Collision counting for the small-overlap route to OP-110.

In a finite loopless arc-dominated digraph, a vertex with a clean out-neighborhood has indegree at least its outdegree.
-/

theorem digraph_clean_center_indegree_ge_outdegree
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (v : α)
    (hclean : ∀ a b, a ≠ b → D.Adj v a → D.Adj v b →
      ∀ p, D.Adj p a → D.Adj p b → p = v) :
    (Finset.univ.filter fun w => D.Adj v w).card ≤
      (Finset.univ.filter fun w => D.Adj w v).card := by
  classical
  let outs : Finset α := Finset.univ.filter fun w => D.Adj v w
  let ins : Finset α := Finset.univ.filter fun w => D.Adj w v
  let f : α → α := fun w => if h : D.Adj v w then Classical.choose (hdom v w h) else v
  have hf : ∀ w, D.Adj v w → D.Adj (f w) v ∧ D.Adj (f w) w := by
    intro w hw
    simpa [f, hw] using Classical.choose_spec (hdom v w hw)
  have hinj : (outs : Set α).InjOn f := by
    intro a ha b hb hab
    have ha' : D.Adj v a := (Finset.mem_filter.mp ha).2
    have hb' : D.Adj v b := (Finset.mem_filter.mp hb).2
    by_contra hne
    have hfa := hf a ha'
    have hfb := hf b hb'
    have heq : f a = v := hclean a b hne ha' hb' (f a) hfa.2 (hab.symm ▸ hfb.2)
    exact hloop v (heq ▸ hfa.1)
  have hm : Set.MapsTo f (outs : Set α) (ins : Set α) := by
    intro w hw
    have hw' : D.Adj v w := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf w hw').1⟩
  exact Finset.card_le_card_of_injOn f hm hinj
