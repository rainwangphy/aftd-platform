import AFTD.Prelude

/-!
# op861_third_roots_subset_sum_norm

Topic: graphs   Node: 4b5b7222818c

Provenance: helper lemma. Elementary complex identity used in op861_order_three_character_sum_bound.

For a nontrivial complex cube root of unity of norm one, every sum of a subset of 1, u, and u squared has norm at most one.
-/

open scoped BigOperators

theorem op861_third_roots_subset_sum_norm (u : ℂ) (hu : u ^ 3 = 1)
    (hne : u ≠ 1) (hnorm : ‖u‖ = 1) (a b c : Bool) :
    ‖(if a then (1 : ℂ) else 0) + (if b then u else 0) + (if c then u ^ 2 else 0)‖ ≤ 1 := by
  have hfac : (u - 1) * (u ^ 2 + u + 1) = 0 := by
    calc
      _ = u ^ 3 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hu
  have hpoly : u ^ 2 + u + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  have h12 : 1 + u = -(u ^ 2) := by linear_combination hpoly
  have h13 : 1 + u ^ 2 = -u := by linear_combination hpoly
  have h23 : u + u ^ 2 = -1 := by linear_combination hpoly
  cases a <;> cases b <;> cases c <;>
    simp [h12, h13, h23, hnorm, norm_pow]
