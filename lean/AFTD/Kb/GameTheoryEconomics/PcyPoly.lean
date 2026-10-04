import AFTD.Prelude

/-!
# pcy_poly

Topic: equilibria   Node: bf144c075cca

The cleared fixed-point polynomial A B - y C E of the three-type instance.
-/

/-- The cleared fixed-point polynomial of the three-type instance: with `s_i = c_i + y^4` for `c = (128, 64, 8)`, it is `A * B - y * C * E` where `A, B, C, E` are the cleared numerators and denominators of the two venue impacts. -/
noncomputable def pcy_poly (y : ℝ) : ℝ :=
  ((3 / 10 * 1 / 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 * 2 / 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
      (13 / 20 * 8 / 8) * ((128 + y ^ 4) * (64 + y ^ 4))) *
    ((3 / 10 * 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 * 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
      (13 / 20 * 8) * ((128 + y ^ 4) * (64 + y ^ 4))) -
  y * ((3 / 10 * 1 * 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 * 2 * 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
      (13 / 20 * 8 * 8) * ((128 + y ^ 4) * (64 + y ^ 4))) *
    ((3 / 10 / 128) * ((64 + y ^ 4) * (8 + y ^ 4)) + (1 / 20 / 64) * ((128 + y ^ 4) * (8 + y ^ 4)) +
      (13 / 20 / 8) * ((128 + y ^ 4) * (64 + y ^ 4)))
