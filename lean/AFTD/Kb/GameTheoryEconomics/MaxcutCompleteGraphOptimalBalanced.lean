import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe

/-!
# maxcut_complete_graph_optimal_balanced

Topic: equilibria   Node: 530a3f809583

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

In an optimal k-colouring of the complete graph K_n, any two colour classes differ in size by at most one: a vertex whose class has a vertices has a - 1 monochromatic neighbours, and maxcut_optimal_same_color_le says that this is at most the number of neighbours of any other colour, i.e. at most the size of any other class.
-/

/-- Optimal colourings of the complete graph are balanced: colour class sizes differ by at most one. -/
theorem maxcut_complete_graph_optimal_balanced {n k : ℕ} (σ : Fin n → Fin k) (hopt : is_maxcut_optimal (⊤ : SimpleGraph (Fin n)) σ) : ∀ c c' : Fin k, (Finset.univ.filter fun v => σ v = c).card ≤ (Finset.univ.filter fun v => σ v = c').card + 1 := by
  intro c c'
  by_cases h : ∃ v, σ v = c
  · rcases h with ⟨v, hv⟩
    have h1 := maxcut_optimal_same_color_le (⊤ : SimpleGraph (Fin n)) σ hopt v c'
    rw [hv] at h1
    have h_erase : (Finset.univ.filter fun w => (⊤ : SimpleGraph (Fin n)).Adj v w ∧ σ w = c) =
        (Finset.univ.filter fun w => σ w = c).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, SimpleGraph.top_adj]
      tauto
    have h_card_erase : ((Finset.univ.filter fun w => σ w = c).erase v).card =
        (Finset.univ.filter fun w => σ w = c).card - 1 := by
      apply Finset.card_erase_of_mem
      simp [hv]
    have h_le : (Finset.univ.filter fun w => (⊤ : SimpleGraph (Fin n)).Adj v w ∧ σ w = c').card ≤
        (Finset.univ.filter fun w => σ w = c').card := by
      apply Finset.card_le_card
      intro w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hw
      exact hw.2
    rw [h_erase, h_card_erase] at h1
    omega
  · have h_empty : (Finset.univ.filter fun v => σ v = c).card = 0 := by
      have : (Finset.univ.filter fun v => σ v = c) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ hx
        exact h ⟨x, hx⟩
      rw [this, Finset.card_empty]
    omega
