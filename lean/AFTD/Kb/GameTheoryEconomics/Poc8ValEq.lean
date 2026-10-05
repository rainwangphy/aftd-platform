import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Val
import AFTD.Kb.GameTheoryEconomics.Poc8U

/-!
# poc8_val_eq

Topic: fair_division   Node: 856043de3d9a

The folded value agrees with the real sum of u over the selected vertices.
-/

theorem poc8_val_eq (P : Fin 8 → Bool) :
    ((poc8_val P : ℕ) : ℝ) = ∑ v ∈ Finset.univ.filter (fun v => P v = true), (poc8_u v : ℝ) := by
  unfold poc8_val
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, List.finRange_succ]
