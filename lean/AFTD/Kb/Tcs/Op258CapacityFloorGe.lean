import AFTD.Prelude
import AFTD.Kb.Tcs.Op258ChooseTwoSubPow

/-!
# op_258_capacity_floor_ge

Topic: combinatorics   Node: 3543c485205f

Provenance: helper lemma. step towards op_258_exists_divergent_capacity_covering

For any natural l ≥ 3 and real x ≥ 1 / 2^{l - 1}, 2^{2l - 2} * x ≤ floor(x * C(2^l, 2)).
-/

/-- For l ≥ 3 and x ≥ 1/2^{l-1}, the integer floor capacity floor(x * C(2^l, 2)) is at least 2^{2l - 2} * x. -/
theorem op_258_capacity_floor_ge (l : ℕ) (hl : 3 ≤ l) (x : ℝ) (hx : 1 / (2 : ℝ)^(l - 1) ≤ x) :
    (2 : ℝ)^(2 * l - 2) * x ≤ ((Nat.floor (x * (((2^l).choose 2 : ℕ) : ℝ)) : ℕ) : ℝ) := by
  have h1 : (2 : ℝ) ^ (l - 1) ≤ (((2^l).choose 2 : ℕ) : ℝ) - (2 : ℝ) ^ (2 * l - 2) :=
    op_258_choose_two_sub_pow l hl
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (l - 1) := by positivity
  have hxA : 1 ≤ x * (2 : ℝ) ^ (l - 1) := by
    have := (div_le_iff₀ hpos).mp hx
    linarith
  have h2 : (2 : ℝ) ^ (2 * l - 2) * x ≤ x * (((2^l).choose 2 : ℕ) : ℝ) - 1 := by
    nlinarith
  have h3 : x * (((2^l).choose 2 : ℕ) : ℝ) - 1 < ((Nat.floor (x * (((2^l).choose 2 : ℕ) : ℝ)) : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  exact le_of_lt (lt_of_le_of_lt h2 h3)
