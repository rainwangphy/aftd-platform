import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundy

/-!
# op_1600_slow_exact_nim_k3_ones

Topic: combinatorial_games   Node: a208b00ab038

Provenance: formalization of a published result. Source: arXiv:2611.14546 after Corollary 1

In slow exact 3-Nim on 5 piles, the all-ones position fun _ : Fin 5 => 1 has Sprague-Grundy value 1.
-/

/-- Sprague-Grundy value of the all-ones position in slow exact 3-Nim on 5 piles is 1. -/
theorem op_1600_slow_exact_nim_k3_ones :
    slow_exact_nim_grundy 3 5 (fun _ : Fin 5 => 1) = 1 := by
  rfl
