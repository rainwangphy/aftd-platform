import AFTD.Prelude

/-!
# simple_graph_triangle_free_independent_neighborhood_cover

Topic: combinatorics   Node: d538c02bff46

Provenance: helper lemma. Neighborhood gluing approach for OP-926, https://arxiv.org/abs/2401.00392; elementary independent-set covering condition.

In a finite triangle-free graph with no independent set of size k, let s be an independent set all of whose vertices are non-neighbors of v, and let t be the neighbors of v having no neighbors in s. Then |s| + |t| < k.
-/

theorem simple_graph_triangle_free_independent_neighborhood_cover {α : Type*} [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (k : ℕ) (htri : G.CliqueFree 3) (hfree : Gᶜ.CliqueFree k)
    (v : α) (s t : Finset α) (hs : G.IsIndepSet s)
    (hns : ∀ x ∈ s, ¬ G.Adj v x)
    (ht : ∀ w, w ∈ t ↔ G.Adj v w ∧ ∀ x ∈ s, ¬ G.Adj w x) :
    s.card + t.card < k := by
  classical
  have hdisj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro x hxs hxt
    exact hns x hxs ((ht x).mp hxt).1
  have htind : G.IsIndepSet t := by
    apply (G.isIndepSet_neighborSet_of_triangleFree htri v).mono
    intro x hx
    exact ((ht x).mp hx).1
  have hst : G.IsIndepSet (s ∪ t : Finset α) := by
    intro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hs hx hy hxy
    · exact fun hadj => ((ht y).mp hy).2 x hx hadj.symm
    · exact fun hadj => ((ht x).mp hx).2 y hy hadj
    · exact htind hx hy hxy
  by_contra hn
  have hle : k ≤ (s ∪ t).card := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hle
  apply hfree u
  apply (Gᶜ.isNClique_iff).2
  constructor
  · rw [SimpleGraph.isClique_compl]
    exact hst.mono (by exact_mod_cast hus)
  · exact huc
