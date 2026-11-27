import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsStrongFef1
import AFTD.Kb.GameTheoryEconomics.IsFefx
import AFTD.Kb.GameTheoryEconomics.IsHereditary
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.Charity

/-!
# exists_strong_fef1_not_fefx_one_agent

Topic: fair_division   Node: a44958dd7290

Provenance: helper lemma. arXiv:2611.34488, Proposition 2.4

There exists an instance with one agent, nonnegative additive valuation, unit-size goods under a budget constraint (hereditary family of bundles of size at most B), and an allocation that satisfies strong FEF1 but fails FEFx.
-/

/-- Strong FEF1 does not imply FEFx, even for one agent with unit sizes under budget constraints. -/
theorem exists_strong_fef1_not_fefx_one_agent :
    ∃ (m : ℕ) (v : Fin 1 → Fin m → ℝ) (_hv : ∀ i g, 0 ≤ v i g)
      (B : ℝ) (A : Fin 1 → Finset (Fin m)),
    let F : Fin 1 → Set (Finset (Fin m)) := fun _ => {S | (S.card : ℝ) ≤ B}
    (∀ i, is_hereditary (F i)) ∧
    is_strong_fef1 v F A ∧ ¬ is_fefx v F A := by
  refine ⟨3, fun _ => ![1, 2, 1], ?_, 1, fun _ => {0}, ?_⟩
  · intro i g
    fin_cases g <;> simp
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · simp
    · intro S T hS hTS
      change (S.card : ℝ) ≤ 1 at hS
      change (T.card : ℝ) ≤ 1
      have h : (T.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hTS
      linarith
  · intro i D hD hne
    have hchar : charity (fun _ : Fin 1 => ({0} : Finset (Fin 3))) = ({1,2} : Finset (Fin 3)) := by
      decide
    have hD' : D = ({1,2} : Finset (Fin 3)) := by
      rcases hD with ⟨j, hj, hDj⟩ | hD
      · exact absurd (Subsingleton.elim j i) hj
      · rw [hD]; exact hchar
    refine ⟨⟨1, by norm_num⟩, ?_, ?_⟩
    · rw [hD']; decide
    · intro T hT hTF
      have hTe : D.erase ⟨1, by norm_num⟩ = ({2} : Finset (Fin 3)) := by
        rw [hD']; decide
      rw [hTe, Finset.subset_singleton_iff] at hT
      have hA : additive_valuation ((fun _ => ![1,2,1]) i) ((fun _ => {0}) i) = 1 := by
        simp [additive_valuation]
      rw [hA]
      rcases hT with h | h
      · rw [h]; simp [additive_valuation]
      · rw [h]; simp [additive_valuation]
  · intro h
    have hchar : charity (fun _ : Fin 1 => ({0} : Finset (Fin 3))) = ({1,2} : Finset (Fin 3)) := by
      decide
    have h1 := h 0 ({1,2} : Finset (Fin 3)) (Or.inr hchar) ({1} : Finset (Fin 3))
      (by decide) (by simp)
    simp [additive_valuation] at h1
