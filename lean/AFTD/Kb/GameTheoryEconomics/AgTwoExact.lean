import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame
import AFTD.Kb.GameTheoryEconomics.AGGameNormalized
import AFTD.Kb.GameTheoryEconomics.AGGameLipschitz
import AFTD.Kb.GameTheoryEconomics.AGGamePureNE
import AFTD.Kb.GameTheoryEconomics.AgTwoUpper
import AFTD.Kb.GameTheoryEconomics.AgMP
import AFTD.Kb.GameTheoryEconomics.AgMPNormalized
import AFTD.Kb.GameTheoryEconomics.AgMPLipschitz
import AFTD.Kb.GameTheoryEconomics.AgMPNoPureNE

/-!
# ag_two_exact

Topic: equilibria   Node: 3bd7d0a5ded5

Exact answer for two strategies. For anonymous games with s = 2 strategies the best possible pure approximation is exactly 2λ = sλ: every λ-Lipschitz game has a pure 2λ-equilibrium, and (normalised, 1/2-Lipschitz) matching pennies has no pure ε-equilibrium with ε < 2λ.
-/

/-- **Exact answer for two strategies.** For anonymous games with `s = 2` strategies the best possible pure approximation is exactly `2λ = sλ`: every `λ`-Lipschitz game has a pure `2λ`-equilibrium, and (normalised, `1/2`-Lipschitz) matching pennies has no pure `ε`-equilibrium with `ε < 2λ`. -/
theorem ag_two_exact :
    (∀ (n : ℕ) (G : AGGame n 2) (lam : ℚ), 0 ≤ lam → G.Lipschitz lam →
        ∃ σ : Fin n → Fin 2, G.PureNE (2 * lam) σ) ∧
    (∃ G : AGGame 2 2, G.Normalized ∧ G.Lipschitz (1 / 2) ∧
        ∀ ε : ℚ, ε < 2 * (1 / 2) → ∀ σ : Fin 2 → Fin 2, ¬ G.PureNE ε σ) :=
  ⟨fun _ G lam hlam hL => ag_two_upper G lam hlam hL,
    ⟨agMP, agMP_normalized, agMP_lipschitz, agMP_no_pureNE⟩⟩
