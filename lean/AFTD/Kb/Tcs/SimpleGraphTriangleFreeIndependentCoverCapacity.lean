import AFTD.Prelude

/-!
# simple_graph_triangle_free_independent_cover_capacity

Topic: combinatorics   Node: 5bbe91990566

Provenance: helper lemma. Independent-set covering route for OP-926; the sets associated with t lie in its independent neighborhood.

In a finite triangle-free graph with no independent k-set, let S and T be disjoint finite vertex sets. For each t in T let J(t) be an independent subset of T. If every vertex x in S has a neighbor t in T such that x has no neighbor in J(t), then |S| plus the sum of the sizes of the J(t) is at most (k − 1)|T|.
-/

theorem simple_graph_triangle_free_independent_cover_capacity {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (k : ℕ) (htri : G.CliqueFree 3) (hfree : Gᶜ.CliqueFree k)
    (S T : Finset α) (J : α → Finset α) (hST : Disjoint S T)
    (hJsub : ∀ t ∈ T, J t ⊆ T)
    (hJind : ∀ t ∈ T, G.IsIndepSet (J t))
    (hcover : ∀ x ∈ S, ∃ t ∈ T, G.Adj t x ∧ ∀ y ∈ J t, ¬ G.Adj x y) :
    S.card + (∑ t ∈ T, (J t).card) ≤ (k - 1) * T.card := by
  classical
  let P : α → Finset α := fun t => S.filter (fun x => G.Adj t x ∧ ∀ y ∈ J t, ¬ G.Adj x y)
  have hpoint (t : α) (ht : t ∈ T) : (P t).card + (J t).card < k := by
    have hdisj : Disjoint (P t) (J t) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.disjoint_left.mp hST) ((Finset.mem_filter.mp hx).1) ((hJsub t ht) hy)
    have hPi : G.IsIndepSet (P t) := by
      apply (G.isIndepSet_neighborSet_of_triangleFree htri t).mono
      intro x hx
      exact ((Finset.mem_filter.mp hx).2).1
    have hU : G.IsIndepSet ((P t ∪ J t : Finset α) : Set α) := by
      intro x hx y hy hxy
      simp only [Finset.coe_union, Set.mem_union] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hPi hx hy hxy
      · exact fun h => ((Finset.mem_filter.mp hx).2).2 y hy h
      · exact fun h => ((Finset.mem_filter.mp hy).2).2 x hx h.symm
      · exact hJind t ht hx hy hxy
    by_contra hn
    have hlarge : k ≤ (P t ∪ J t).card := by
      rw [Finset.card_union_of_disjoint hdisj]
      omega
    obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hlarge
    apply hfree u
    apply (Gᶜ.isNClique_iff).2
    constructor
    · rw [SimpleGraph.isClique_compl]
      exact hU.mono (by exact_mod_cast hus)
    · exact huc
  have hsum : (∑ t ∈ T, ((P t).card + (J t).card)) ≤ ∑ _t ∈ T, (k - 1) := by
    apply Finset.sum_le_sum
    intro t ht
    have hp := hpoint t ht
    omega
  have hsum' : (∑ t ∈ T, (P t).card) + (∑ t ∈ T, (J t).card) ≤ (k - 1) * T.card := by
    simpa [Finset.sum_add_distrib, mul_comm] using hsum
  have hS : S ⊆ T.biUnion P := by
    intro x hx
    obtain ⟨t, ht, hadj, hcross⟩ := hcover x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx, hadj, hcross⟩
  have hsize : S.card ≤ ∑ t ∈ T, (P t).card :=
    (Finset.card_le_card hS).trans Finset.card_biUnion_le
  omega
