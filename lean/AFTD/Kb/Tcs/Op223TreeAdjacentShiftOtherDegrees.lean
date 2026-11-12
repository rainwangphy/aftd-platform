import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph

/-!
# op223_tree_adjacent_shift_other_degrees

Topic: graphs   Node: bcf584a4a9af

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; corrected versions of auxiliary statements retired by experiments 23031 and 23032

An adjacent generalized shift in a finite tree preserves the degree of every vertex other than its two endpoints.
-/

private lemma op223_tree_adjacent_shift_other_degrees_no_triangle {V : Type*} (T : SimpleGraph V) {u v x : V} (hT : T.IsTree)
    (huv : T.Adj u v) (hvx : T.Adj v x) : ¬ T.Adj u x := by
  intro hux
  have h1 : (SimpleGraph.Walk.cons hvx SimpleGraph.Walk.nil : T.Walk v x).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [hvx.ne]⟩
  have hp : (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvx SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨h1, ?_⟩
    simp [huv.ne, hux.ne]
  have key := hT.isAcyclic.eq_snd_of_adj_start (p := SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvx SimpleGraph.Walk.nil)) hp hux (SimpleGraph.Walk.end_mem_support _)
  rw [SimpleGraph.Walk.snd_cons] at key
  exact hvx.ne' key

set_option maxHeartbeats 1000000 in
private lemma op223_tree_adjacent_shift_other_degrees_mem_del {V : Type*} (T : SimpleGraph V) (u v x y : V)
    (hx1 : x ≠ u) (hx2 : x ≠ v) :
    (∃ z : V, s(x, y) = s(v, z) ∧ T.Adj v z ∧ z ≠ u) ↔ (y = v ∧ T.Adj v x) := by
  constructor
  · rintro ⟨z, he, hadj, hzu⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 hx2
    · subst h1; subst h2; exact ⟨rfl, hadj⟩
  · rintro ⟨rfl, hadj⟩
    exact ⟨x, Sym2.eq_swap, hadj, hx1⟩

set_option maxHeartbeats 1000000 in
private lemma op223_tree_adjacent_shift_other_degrees_mem_add {V : Type*} (T : SimpleGraph V) (u v x y : V)
    (hx1 : x ≠ u) :
    (∃ z : V, s(x, y) = s(u, z) ∧ T.Adj v z ∧ z ≠ u) ↔ (y = u ∧ T.Adj v x) := by
  constructor
  · rintro ⟨z, he, hadj, hzu⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 hx1
    · subst h1; subst h2; exact ⟨rfl, hadj⟩
  · rintro ⟨rfl, hadj⟩
    exact ⟨x, Sym2.eq_swap, hadj, hx1⟩

theorem op223_tree_adjacent_shift_other_degrees {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) (u v : V) (hT : T.IsTree) (huv : T.Adj u v) : ∀ x : V, x ≠ u → x ≠ v → Nat.card ((gts_graph T u v u).neighborSet x) = Nat.card (T.neighborSet x) := by
  intro x hx1 hx2
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have hS : ∀ y : V, (∃ z : V, s(x, y) = s(v, z) ∧ T.Adj v z ∧ z ≠ u) ↔ (y = v ∧ T.Adj v x) :=
    fun y => op223_tree_adjacent_shift_other_degrees_mem_del T u v x y hx1 hx2
  have hE : ∀ y : V, (∃ z : V, s(x, y) = s(u, z) ∧ T.Adj v z ∧ z ≠ u) ↔ (y = u ∧ T.Adj v x) :=
    fun y => op223_tree_adjacent_shift_other_degrees_mem_add T u v x y hx1
  by_cases hvx : T.Adj v x
  · have hne : ¬ T.Adj u x := op223_tree_adjacent_shift_other_degrees_no_triangle T hT huv hvx
    have hset : (gts_graph T u v u).neighborSet x = insert u (T.neighborSet x \ {v}) := by
      ext y
      simp only [gts_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
        SimpleGraph.fromEdgeSet_adj, SimpleGraph.mem_neighborSet, Set.mem_ofPred_eq,
        Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff, hS y, hE y]
      constructor
      · rintro (⟨hadj, hnot⟩ | ⟨⟨rfl, -⟩, -⟩)
        · exact Or.inr ⟨hadj, fun hy => hnot ⟨hy, hvx⟩⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨hadj, hyv⟩)
        · exact Or.inr ⟨⟨rfl, hvx⟩, hx1⟩
        · exact Or.inl ⟨hadj, fun h => hyv h.1⟩
    rw [hset]
    have hu_not : u ∉ T.neighborSet x \ {v} := by
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, SimpleGraph.mem_neighborSet]
      rintro ⟨hadj, -⟩
      exact hne hadj.symm
    rw [Set.ncard_insert_of_notMem hu_not]
    have hv_mem : v ∈ T.neighborSet x := (SimpleGraph.mem_neighborSet T x v).mpr hvx.symm
    rw [(Set.ncard_sdiff_singleton_add_one hv_mem).symm]
  · have hset : (gts_graph T u v u).neighborSet x = T.neighborSet x := by
      ext y
      simp only [gts_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
        SimpleGraph.fromEdgeSet_adj, SimpleGraph.mem_neighborSet, Set.mem_ofPred_eq, hS y, hE y]
      tauto
    rw [hset]
