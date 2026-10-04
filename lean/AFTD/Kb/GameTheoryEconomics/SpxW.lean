import AFTD.Prelude

/-!
# spx_w

Topic: mechanism_design   Node: 1ba3fba42ad9

Probabilities of the four-player instance: 1; 1/10 for 9; 1/300 for 1000; 1/25 for 40.
-/

/-- Probabilities of the support values of the four-player instance. -/
noncomputable def spx_w : Fin 4 → Fin 2 → ℝ := ![![1, 0], ![1 / 10, 9 / 10], ![1 / 300, 299 / 300], ![1 / 25, 24 / 25]]
