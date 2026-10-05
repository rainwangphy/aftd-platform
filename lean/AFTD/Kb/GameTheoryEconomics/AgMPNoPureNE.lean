import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCnt
import AFTD.Kb.GameTheoryEconomics.AGGamePureNE
import AFTD.Kb.GameTheoryEconomics.AgMP
import AFTD.Kb.GameTheoryEconomics.AgMPv
import AFTD.Kb.GameTheoryEconomics.AgMPUEq
import AFTD.Kb.GameTheoryEconomics.AgMPCheck

/-!
# agMP_no_pureNE

Topic: equilibria   Node: a56162c5d68a

In matching pennies every pure profile leaves a player with regret 1 = 2λ.
-/

/-- In matching pennies every pure profile leaves a player with regret `1 = 2λ`. -/
theorem agMP_no_pureNE (ε : ℚ) (hε : ε < 2 * (1 / 2)) (σ : Fin 2 → Fin 2) :
    ¬ agMP.PureNE ε σ := by
  intro h
  have hσ : σ = ![σ 0, σ 1] := by
    funext q; fin_cases q <;> rfl
  obtain ⟨p, j, hpj⟩ := agMP_check (σ 0) (σ 1)
  rw [← hσ] at hpj
  have := h p j
  rw [agMP_u_eq, agMP_u_eq] at this
  have hq : ((agMPv p (σ p) (agCnt σ p) + 1 : ℕ) : ℚ) ≤ (agMPv p j (agCnt σ p) : ℚ) := by
    exact_mod_cast hpj
  push_cast at hq
  linarith
