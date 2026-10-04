import AFTD.Prelude

/-!
# spi_two_point_max_prob

Topic: mechanism_design   Node: a81cac05a760

Proposition 3.1 for a two-point reward (h with probability q, else l): the largest acceptance probability achievable under threshold T (1 if T <= E[X], q(h-l)/(T-l) if E[X] < T <= h, 0 if T > h).
-/

/-- Prop. 3.1 of Tang–Xu–Zhang–Zhu for a two-point reward (`h` with probability `q`, else `l`): the largest probability with which the player can get accepted under threshold `T`. -/
noncomputable def spi_two_point_max_prob (h l q T : ℝ) : ℝ :=
  if T ≤ q * h + (1 - q) * l then 1 else if T ≤ h then q * (h - l) / (T - l) else 0
