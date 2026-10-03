import AFTD.Prelude

/-!
# persuasion_obedience_cost

Topic: mechanism_design   Node: 1b15419ac2c0

Obedience cost C_i(x, a): 1/2 - x_i if a_i = 1, x_i - 1/2 if a_i = 0.
-/

open Finset in
/-- Obedience cost `C_i(x, a)`: `1/2 - x_i` if `a_i = 1`, `x_i - 1/2` if `a_i = 0`. -/
noncomputable def persuasion_obedience_cost {ι : Type*} (i : ι) (x a : ι → Bool) : ℝ :=
  if a i then 1 / 2 - (if x i then 1 else 0) else (if x i then 1 else 0) - 1 / 2
