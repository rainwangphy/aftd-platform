import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costAlphaPos
import AFTD.Kb.GameTheoryEconomics.Ef1costCore
import AFTD.Kb.GameTheoryEconomics.Ef1costEf1OfPair
import AFTD.Kb.GameTheoryEconomics.Ef1costFromCore
import AFTD.Kb.GameTheoryEconomics.Ef1costOptLe
import AFTD.Kb.GameTheoryEconomics.Ef1costPairOk
import AFTD.Kb.GameTheoryEconomics.Ef1costSocialCostEq
import AFTD.Kb.GameTheoryEconomics.IsEf1Chores
import AFTD.Kb.GameTheoryEconomics.IsNormalizedChoresInstance
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# exists_ef1_social_cost_le_opt_add_two_agents

Topic: fair_division   Node: 581fce0b002c

For two agents with normalized additive chores, some EF1 allocation has social cost at most the optimum plus 3 - 2 sqrt 2.
-/

/-- **Upper bound for two agents.** In every normalised two-agent chores instance (any number of chores) there is an EF1 allocation whose social cost exceeds the optimum by at most `3 - 2√2 ≈ 0.1716`. -/
theorem exists_ef1_social_cost_le_opt_add_two_agents {m : ℕ} (c : Fin 2 → Fin m → ℝ)
    (hc : is_normalized_chores_instance c) :
    ∃ σ, is_ef1_chores c σ ∧ ∀ τ, social_cost c σ ≤ social_cost c τ + (3 - 2 * Real.sqrt 2) := by
  classical
  obtain ⟨hc0, hc1⟩ := hc
  set X : Finset (Fin m) := Finset.univ.filter (fun j => c 0 j ≤ c 1 j) with hXdef
  have hmemX : ∀ j, j ∈ X ↔ c 0 j ≤ c 1 j := by intro j; simp [hXdef]
  have hσ0 : ∀ j, (if c 0 j ≤ c 1 j then (0 : Fin 2) else 1) = if j ∈ X then 0 else 1 := by
    intro j; simp only [hmemX]
  have hopt0 : ∀ τ : Fin m → Fin 2, ∑ j, c (if j ∈ X then 0 else 1) j ≤ ∑ j, c (τ j) j := by
    intro τ
    have := ef1cost_opt_le c τ
    simp only [hσ0] at this
    exact this
  by_cases hQ : ef1cost_pair_ok (c 1) Xᶜ X
  · by_cases hP : ef1cost_pair_ok (c 0) X Xᶜ
    · -- the optimum itself is EF1
      refine ⟨fun j => if j ∈ X then 0 else 1, ef1cost_ef1_of_pair c 0 1 (by decide) X hP hQ,
        fun τ => ?_⟩
      rw [ef1cost_social_cost_eq, ef1cost_social_cost_eq]
      linarith [hopt0 τ, ef1cost_alpha_pos]
    · -- agent 0 is not EF1: transfer from agent 0 to agent 1
      have hcore := ef1cost_core (c 1) (c 0) (hc0 1) (hc0 0) (hc1 1) (hc1 0) Xᶜ
        (fun j hj => by
          rw [Finset.mem_compl, hmemX] at hj; linarith)
        (fun j hj => by
          rw [Finset.mem_compl, not_not, hmemX] at hj; exact hj)
        (by have hXX : Xᶜᶜ = X := compl_compl X; rw [hXX]; exact hP)
      refine ef1cost_from_core c 1 0 (by decide) Xᶜ (fun τ => ?_) hcore
      have := hopt0 τ
      have e : ∀ j, (if j ∈ Xᶜ then (1 : Fin 2) else 0) = if j ∈ X then 0 else 1 := by
        intro j
        by_cases h : j ∈ X <;> simp [h]
      simp only [e]
      exact this
  · -- agent 1 is not EF1: transfer from agent 1 to agent 0
    have hcore := ef1cost_core (c 0) (c 1) (hc0 0) (hc0 1) (hc1 0) (hc1 1) X
      (fun j hj => (hmemX j).mp hj)
      (fun j hj => by rw [hmemX] at hj; linarith)
      hQ
    exact ef1cost_from_core c 0 1 (by decide) X hopt0 hcore
