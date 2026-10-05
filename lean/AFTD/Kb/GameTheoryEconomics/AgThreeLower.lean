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
import AFTD.Kb.GameTheoryEconomics.AgCyc3Check
import AFTD.Kb.GameTheoryEconomics.AgCycRegret

/-!
# ag_three_lower

Topic: equilibria   Node: e14eb6bf4939

Three strategies: the lower bound exceeds sλ. The 5-player, 3-strategy cyclic game is normalised and λ = 1/8-Lipschitz, yet has no pure ε-equilibrium for any ε < 4λ (and 4λ > 3λ = sλ).
-/

open Finset in
/-- **Three strategies: the lower bound exceeds `sλ`.** The 5-player, 3-strategy cyclic game is normalised and `λ = 1/8`-Lipschitz, yet has no pure `ε`-equilibrium for any `ε < 4λ` (and `4λ > 3λ = sλ`). -/
theorem ag_three_lower :
    ∃ G : AGGame 5 3, G.Normalized ∧ G.Lipschitz (1 / 8) ∧
      ∀ ε : ℚ, ε < 4 * (1 / 8) → ∀ σ : Fin 5 → Fin 3, ¬ G.PureNE ε σ := by
  refine ⟨agCyc 5 3, agCyc_normalized 3 (by norm_num), agCyc_lipschitz 5 3 (by norm_num), ?_⟩
  intro ε hε σ hNE
  have hsum := agTot_sum σ
  rw [Fin.sum_univ_three] at hsum
  have hc : agTot σ = ![agTot σ 0, agTot σ 1, agTot σ 2] := by
    funext k; fin_cases k <;> rfl
  obtain ⟨i, j, hpos, hreg⟩ := agCyc3_check ⟨agTot σ 0, by omega⟩ ⟨agTot σ 1, by omega⟩
    ⟨agTot σ 2, by omega⟩ (by simpa using hsum)
  simp only at hpos hreg
  rw [← hc] at hpos hreg
  obtain ⟨p, hp⟩ := agCyc_regret σ i j hpos hreg
  have := hNE p j
  linarith
