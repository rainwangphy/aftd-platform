import AFTD.Prelude

/-!
# spx_x

Topic: mechanism_design   Node: 443b7ea5bada

Support values of the four-player instance: X0 = 24/5 surely; X1 in {9, 3}; X2 in {1000, 0}; X3 in {40, 0}.
-/

/-- The four-player instance: `X₀ = 24/5` surely; `X₁ = 9` w.p. 1/10, else 3; `X₂ = 1000` w.p. 1/300, else 0; `X₃ = 40` w.p. 1/25, else 0 (support values). -/
noncomputable def spx_x : Fin 4 → Fin 2 → ℝ := ![![24 / 5, 0], ![9, 3], ![1000, 0], ![40, 0]]
