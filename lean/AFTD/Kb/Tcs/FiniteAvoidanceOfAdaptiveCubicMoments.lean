import AFTD.Prelude

/-!
# finite_avoidance_of_adaptive_cubic_moments

Topic: graphs   Node: 53910bba4e3c

Provenance: helper lemma. OP-306 / IN-338 general-route helpers for the strict prescribed-coloring conjecture in arXiv:2610.22142, Sections3.3.2 and6. Structural analysis of binary factorizations and exact finite averaging in experiments8399,8400,8402,8414. These are conditional certificate or method-diagnostic lemmas, not a new wild-number bound or research advance.

For a natural-valued defect count d on any finite sample space and any positive integer r, put R=r(r+1). If R times sum(d) plus6 times sum(binomial(d,3)) is strictly less than R times the sample-space size plus (4r-2) times sum(binomial(d,2)), some sample has defect count zero.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

private lemma in338_choose_three (d : ℕ) :
    6 * (d.choose 3 : ℝ) = (d : ℝ) * (d - 1) * (d - 2) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [Nat.choose_succ_succ]
    push_cast
    rw [Nat.cast_choose_two]
    nlinarith only [ih]

private lemma in338_cubic_identity (d r : ℕ) :
    (1 - (d : ℝ)) * ((d : ℝ) - r) * ((d : ℝ) - (r + 1)) =
      (r : ℝ) * (r + 1) * (1 - (d : ℝ)) +
        (4 * (r : ℝ) - 2) * (d.choose 2 : ℝ) - 6 * (d.choose 3 : ℝ) := by
  rw [Nat.cast_choose_two]
  nlinarith only [in338_choose_three d]

private lemma in338_cubic_nonpos (d r : ℕ) (hd : 1 ≤ d) :
    (1 - (d : ℝ)) * ((d : ℝ) - r) * ((d : ℝ) - (r + 1)) ≤ 0 := by
  have hpair : 0 ≤ ((d : ℝ) - r) * ((d : ℝ) - (r + 1)) := by
    by_cases h : d ≤ r
    · have h' : (d : ℝ) ≤ r := by exact_mod_cast h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h' : (r : ℝ) + 1 ≤ d := by exact_mod_cast (show r + 1 ≤ d by omega)
      exact mul_nonneg (by linarith) (by linarith)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simpa only [mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hd') hpair

theorem finite_avoidance_of_adaptive_cubic_moments
    {J : Type*} [Fintype J] (d : J → ℕ) (r : ℕ) (hr : 1 ≤ r)
    (h : (r : ℝ) * (r + 1) * (∑ j, (d j : ℝ)) +
        6 * (∑ j, ((d j).choose 3 : ℝ)) <
      (r : ℝ) * (r + 1) * Fintype.card J +
        (4 * (r : ℝ) - 2) * (∑ j, ((d j).choose 2 : ℝ))) :
    ∃ j, d j = 0 := by
  by_contra! hno
  have hp : ∀ j, (r : ℝ) * (r + 1) +
        (4 * (r : ℝ) - 2) * ((d j).choose 2 : ℝ) ≤
      (r : ℝ) * (r + 1) * (d j : ℝ) + 6 * ((d j).choose 3 : ℝ) := by
    intro j
    have hx := in338_cubic_nonpos (d j) r (by have := hno j; omega)
    rw [in338_cubic_identity] at hx
    nlinarith only [hx]
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => hp j)
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum] at hs
  nlinarith only [h, hs]
