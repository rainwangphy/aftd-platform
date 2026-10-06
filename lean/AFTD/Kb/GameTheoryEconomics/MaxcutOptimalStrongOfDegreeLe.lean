import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalStrongUpToDegree
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_optimal_strong_of_degree_le

Topic: equilibria   Node: a7196b9402d8

Provenance: formalization of a published result. Source: arXiv:2610.04948, Corollary 9 (originally arXiv:1810.09278, Proposition 9), stated there for k ≥ 2; the Lean version allows k ≥ 1 (k = 1 is trivial). Proof follows the paper's internal-conflict counting: optimal colorings are Nash, so each vertex has at most one same-colored neighbour, and the deviation identity (Lemma 7) then rules out every strong deviation

For every k ≥ 1: on every finite simple graph whose maximum degree is at most 2k − 1, every optimal coloring of the unweighted Max-k-Cut game is a strong equilibrium. In terms of the open problem, Δ*(k) ≥ 2k − 1.
-/

theorem maxcut_optimal_strong_of_degree_le (k : ℕ) (hk : 1 ≤ k) :
    maxcut_optimal_strong_up_to_degree k (2 * k - 1) := by
  classical
  intro V _ G _ hdeg σ hopt S τ hdev
  obtain ⟨hne, hagree, hgain⟩ := hdev
  -- at most one neighbour shares each vertex's color
  have hmono : ∀ v, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 1 := by
    intro v
    have hsum : (Finset.univ.filter fun w => G.Adj v w).card =
        ∑ c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := Finset.univ)
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
      simp only [Finset.filter_filter]
    have hdv : (Finset.univ.filter fun w => G.Adj v w).card ≤ 2 * k - 1 := by
      have := hdeg v
      rwa [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
        at this
    have hlow : ∑ _c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤
        ∑ c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card :=
      Finset.sum_le_sum fun c _ => maxcut_optimal_same_color_le G σ hopt v c
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlow
    by_contra hc
    have : k * 2 ≤ k * (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card :=
      Nat.mul_le_mul_left k (by omega)
    omega
  have hS := maxcut_welfare_split G σ S
  have hT := maxcut_welfare_split G τ S
  have hC : ∑ x ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj x w ∧ τ w ≠ τ x then 1 else 0 : ℕ) =
      ∑ x ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj x w ∧ σ w ≠ σ x then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun w hw => ?_
    rw [hagree x (Finset.mem_compl.1 hx), hagree w (Finset.mem_compl.1 hw)]
  have hUS := maxcut_utility_sum_split G σ S
  have hUT := maxcut_utility_sum_split G τ S
  have hgains : ∑ v ∈ S, maxcut_utility G σ v + S.card ≤ ∑ v ∈ S, maxcut_utility G τ v := by
    have := Finset.sum_le_sum fun v hv => Nat.succ_le_of_lt (hgain v hv)
    simpa [Finset.sum_add_distrib] using this
  have hpt : ∀ v w, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ) ≤
      (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) +
        (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) := by
    intro v w
    rcases em (G.Adj v w ∧ τ w ≠ τ v) with h1 | h1
    · rw [if_pos h1]
      rcases em (σ w = σ v) with h2 | h2
      · rw [if_pos (⟨h1.1, h2⟩ : G.Adj v w ∧ σ w = σ v)]; omega
      · rw [if_pos (⟨h1.1, h2⟩ : G.Adj v w ∧ σ w ≠ σ v)]; omega
    · rw [if_neg h1]; omega
  have hA : ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ) ≤
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) + S.card := by
    calc ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ)
        ≤ ∑ v ∈ S, (∑ w ∈ S, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) + 1) := by
          refine Finset.sum_le_sum fun v _ => ?_
          calc ∑ w ∈ S, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ)
              ≤ ∑ w ∈ S, ((if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) +
                  (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)) :=
                Finset.sum_le_sum fun w _ => hpt v w
            _ = ∑ w ∈ S, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) +
                  ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) :=
                Finset.sum_add_distrib
            _ ≤ _ := by
                have : ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) ≤ 1 := by
                  calc ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)
                      ≤ ∑ w, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) :=
                        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
                    _ = (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card :=
                        (Finset.card_filter _ _).symm
                    _ ≤ 1 := hmono v
                omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hcard : 1 ≤ S.card := Finset.card_pos.2 hne
  have hopt' := hopt τ
  omega
