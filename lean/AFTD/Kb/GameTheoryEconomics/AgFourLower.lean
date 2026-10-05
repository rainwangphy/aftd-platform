import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame
import AFTD.Kb.GameTheoryEconomics.AGGameNormalized
import AFTD.Kb.GameTheoryEconomics.AGGameLipschitz
import AFTD.Kb.GameTheoryEconomics.AGGamePureNE
import AFTD.Kb.GameTheoryEconomics.AgCyc
import AFTD.Kb.GameTheoryEconomics.AgCycLipschitz
import AFTD.Kb.GameTheoryEconomics.AgCycNormalized
import AFTD.Kb.GameTheoryEconomics.AgTot
import AFTD.Kb.GameTheoryEconomics.AgTotSum
import AFTD.Kb.GameTheoryEconomics.AgCyc4Check
import AFTD.Kb.GameTheoryEconomics.AgCycRegret

/-!
# ag_four_lower

Topic: equilibria   Node: cddc782c4f86

Four strategies: the lower bound sλ is attained. The 5-player, 4-strategy cyclic game is normalised and λ = 1/8-Lipschitz, yet has no pure ε-equilibrium for any ε < 4λ = sλ.
-/

open Finset in
/-- **Four strategies: the lower bound `sλ` is attained.** The 5-player, 4-strategy cyclic game is normalised and `λ = 1/8`-Lipschitz, yet has no pure `ε`-equilibrium for any `ε < 4λ = sλ`. -/
theorem ag_four_lower :
    ∃ G : AGGame 5 4, G.Normalized ∧ G.Lipschitz (1 / 8) ∧
      ∀ ε : ℚ, ε < 4 * (1 / 8) → ∀ σ : Fin 5 → Fin 4, ¬ G.PureNE ε σ := by
  refine ⟨agCyc 5 4, agCyc_normalized 4 (by norm_num), agCyc_lipschitz 5 4 (by norm_num), ?_⟩
  intro ε hε σ hNE
  have hsum := agTot_sum σ
  rw [Fin.sum_univ_four] at hsum
  have hc : agTot σ = ![agTot σ 0, agTot σ 1, agTot σ 2, agTot σ 3] := by
    funext k; fin_cases k <;> rfl
  obtain ⟨i, j, hpos, hreg⟩ := agCyc4_check ⟨agTot σ 0, by omega⟩ ⟨agTot σ 1, by omega⟩
    ⟨agTot σ 2, by omega⟩ ⟨agTot σ 3, by omega⟩ (by simpa using hsum)
  simp only at hpos hreg
  rw [← hc] at hpos hreg
  obtain ⟨p, hp⟩ := agCyc_regret σ i j hpos hreg
  have := hNE p j
  linarith
