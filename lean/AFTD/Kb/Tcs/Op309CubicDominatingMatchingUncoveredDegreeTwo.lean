import AFTD.Prelude

/-!
# op309_cubic_dominating_matching_uncovered_degree_two

Topic: graphs   Node: 0c5a907845f5

Provenance: helper lemma. Structural reduction of the induced paired-domination route to OP-309; examples 31752 and 31819.

In a finite cubic simple graph whose matching endpoints dominate all vertices, every uncovered vertex has at most two uncovered neighbors.
-/

theorem op309_cubic_dominating_matching_uncovered_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 3)
    (M : Finset G.edgeSet) :
    let covered : V → Prop := fun v => ∃ e ∈ M, v ∈ e.1
    (∀ v : V, covered v ∨ ∃ u : V, G.Adj v u ∧ covered u) →
    ∀ v a b c : V, ¬ covered v → [a,b,c].Nodup →
      G.Adj v a → G.Adj v b → G.Adj v c → covered a ∨ covered b ∨ covered c := by
  intro covered hdom v a b c hnc hnd hva hvb hvc
  rcases hdom v with hv_cov | ⟨u, hvu, hu_cov⟩
  · exact False.elim (hnc hv_cov)
  · have hcard_abc : ({a, b, c} : Finset V).card = 3 := by
      have : a ≠ b ∧ a ≠ c ∧ b ≠ c := by aesop
      rcases this with ⟨hab, hac, hbc⟩
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hbc]
      · simp [hab, hac]
    have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [SimpleGraph.mem_neighborFinset]; exact hva
      · rw [SimpleGraph.mem_neighborFinset]; exact hvb
      · rw [SimpleGraph.mem_neighborFinset]; exact hvc
    have hcard_N : (G.neighborFinset v).card = 3 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree]
    have heq : ({a, b, c} : Finset V) = G.neighborFinset v := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard_N, hcard_abc]
    have hu_mem : u ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hvu
    rw [← heq] at hu_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem
    rcases hu_mem with rfl | rfl | rfl
    · left; exact hu_cov
    · right; left; exact hu_cov
    · right; right; exact hu_cov
