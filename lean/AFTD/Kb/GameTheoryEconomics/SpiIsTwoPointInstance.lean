import AFTD.Prelude

/-!
# spi_is_two_point_instance

Topic: mechanism_design   Node: 73ea7dd8bbb0

Two-point instances: every player's reward is x_i0 with probability w_i0 and x_i1 otherwise, with 0 <= x_i1 <= x_i0.
-/

/-- Two-point instances: every player's reward is `x i 0` with probability `w i 0` and `x i 1` otherwise, with `0 ≤ x i 1 ≤ x i 0`. -/
def spi_is_two_point_instance {N : ℕ} (x w : Fin N → Fin 2 → ℝ) : Prop :=
  ∀ i, 0 ≤ x i 1 ∧ x i 1 ≤ x i 0 ∧ 0 ≤ w i 0 ∧ w i 0 ≤ 1 ∧ w i 1 = 1 - w i 0
