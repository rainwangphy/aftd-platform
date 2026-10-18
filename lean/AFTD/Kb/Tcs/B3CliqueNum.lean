import AFTD.Prelude
import AFTD.Kb.Tcs.B3Graph
import AFTD.Kb.Tcs.B3GraphAdj

/-!
# b3_cliqueNum

Topic: graphs   Node: a7fb94801170

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), Sec. 2.2 (structural value of ω for B_3) / Theorem 3.1; serves b3_sqrt_trace_quotient_sq_le_clique_bound

The clique number of B_3(n_0, n_1, n_2) is max(n_0 + n_2, n_1 + n_2).
-/

theorem b3_card_pair (n : Fin 3 → ℕ) (i : Fin 3) (hi : i ≠ 2) :
    (({i, 2} : Finset (Fin 3)).sigma fun j => (Finset.univ : Finset (Fin (n j)))).card
      = n i + n 2 := by
  rw [Finset.card_sigma, Finset.sum_pair hi]
  simp

theorem b3_pair_isClique (n : Fin 3 → ℕ) (i : Fin 3) :
    (b3_graph n).IsClique
      ((({i, 2} : Finset (Fin 3)).sigma fun j => (Finset.univ : Finset (Fin (n j)))) :
        Set (Σ j : Fin 3, Fin (n j))) := by
  intro x hx y hy hxy
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hx hy
  rw [b3_graph_adj]
  refine ⟨hxy, ?_⟩
  rcases hx.1 with h | h <;> rcases hy.1 with h' | h' <;> simp [h, h']

theorem b3_cliqueNum (n : Fin 3 → ℕ) :
    (b3_graph n).cliqueNum = max (n 0 + n 2) (n 1 + n 2) := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (b3_graph n).exists_isNClique_cliqueNum
    rw [← hs.card_eq]
    by_cases h0 : ∃ x ∈ s, x.1 = 0
    · -- then no vertex of block 1
      obtain ⟨x, hx, hx0⟩ := h0
      have hsub : s ⊆ ({0, 2} : Finset (Fin 3)).sigma fun j => Finset.univ := by
        intro y hy
        simp only [Finset.mem_sigma, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
          and_true]
        by_contra hne
        push Not at hne
        have hy1 : y.1 = 1 := by omega
        have hxy : x ≠ y := by rintro rfl; rw [hx0] at hy1; exact absurd hy1 (by decide)
        have := (b3_graph_adj n x y).1 (hs.isClique hx hy hxy)
        rcases this.2 with h | h | h <;> simp_all
      calc s.card ≤ _ := Finset.card_le_card hsub
        _ = n 0 + n 2 := b3_card_pair n 0 (by decide)
        _ ≤ _ := le_max_left _ _
    · push Not at h0
      have hsub : s ⊆ ({1, 2} : Finset (Fin 3)).sigma fun j => Finset.univ := by
        intro y hy
        simp only [Finset.mem_sigma, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
          and_true]
        have := h0 y hy
        omega
      calc s.card ≤ _ := Finset.card_le_card hsub
        _ = n 1 + n 2 := b3_card_pair n 1 (by decide)
        _ ≤ _ := le_max_right _ _
  · apply max_le
    · rw [← b3_card_pair n 0 (by decide)]
      exact (b3_pair_isClique n 0).card_le_cliqueNum
    · rw [← b3_card_pair n 1 (by decide)]
      exact (b3_pair_isClique n 1).card_le_cliqueNum
