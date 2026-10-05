import AFTD.Prelude

/-!
# team_w

Topic: algorithms   Node: 713e0399a0b9

Edge probabilities on the cycle i → i+1 (mod n): 3/4, 3/4, 0, 1, 0, 1, …, 1, 0.
-/

/-- Edge probabilities on the cycle `i → i+1 (mod n)`: `3/4, 3/4, 0, 1, 0, 1, …, 1, 0`. -/
noncomputable def team_w {m : ℕ} (i : Fin (2 * m + 3)) : ℝ :=
  if i.val ≤ 1 then 3 / 4 else if i.val % 2 = 0 then 0 else 1
