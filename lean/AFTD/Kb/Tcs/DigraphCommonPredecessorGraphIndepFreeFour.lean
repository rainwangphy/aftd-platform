import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_common_predecessor_graph_indep_free_four

Topic: graphs   Node: 55c65b545862

Provenance: helper lemma. The independence argument of arXiv:2610.11517 Proposition 4.3, specialized to four cycles.

If each in-neighborhood of a finite digraph contains a directed cycle and the digraph has no four disjoint directed cycles, then its common-predecessor graph has no independent set of size four.
-/

theorem digraph_common_predecessor_graph_indep_free_four
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α)
    (hin : ∀ a, ∃ C : Finset α, digraph_directed_cycle_on D C ∧ ∀ v ∈ C, D.Adj v a)
    (hno : ¬ ∃ s : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j))) :
    (digraph_common_predecessor_graph D).IndepSetFree 4 := by
  classical
  intro t ht
  let e : t ≃ Fin 4 := Finset.equivFinOfCardEq ht.card_eq
  let f : Fin 4 → α := fun i => (e.symm i).val
  have hfmem : ∀ i, f i ∈ t := fun i => (e.symm i).property
  have hfinj : Function.Injective f := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact hij
  let c : Fin 4 → Finset α := fun i => Classical.choose (hin (f i))
  have hc : ∀ i, digraph_directed_cycle_on D (c i) ∧ ∀ v ∈ c i, D.Adj v (f i) := by
    intro i
    exact Classical.choose_spec (hin (f i))
  apply hno
  refine ⟨c, fun i => (hc i).1, ?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hne : f i ≠ f j := fun h => hij (hfinj h)
  have hn : ¬ (digraph_common_predecessor_graph D).Adj (f i) (f j) :=
    ht.isIndepSet (hfmem i) (hfmem j) hne
  apply hn
  exact ⟨hne, x, (hc i).2 x hxi, (hc j).2 x hxj⟩
