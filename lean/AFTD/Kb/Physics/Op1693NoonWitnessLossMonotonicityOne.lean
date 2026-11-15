import AFTD.Prelude
import AFTD.Kb.Physics.NoonRealignWitness
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# op_1693_noon_witness_loss_monotonicity_one

Topic: quantum_mechanics   Node: 3613214643c2

Provenance: formalization of a published result. Source: arXiv:2611.17021

For N = 1 and any balance parameter q in the open interval (0, 1) and transmissivities x, y in the open interval (0, 1), if noon_realign_witness 1 q x y > 1, then the partial derivatives of noon_realign_witness 1 q at x and y are non-negative (0 ≤ deriv (fun u => noon_realign_witness 1 q u y) x and 0 ≤ deriv (fun v => noon_realign_witness 1 q x v) y), and the detection region is upward closed: for 0 < x ≤ x' < 1 and 0 < y ≤ y' < 1, noon_realign_witness 1 q x y > 1 implies noon_realign_witness 1 q x' y' > 1.
-/

private lemma op_1693_noon_witness_loss_monotonicity_one_deriv_quadratic (a b c x : ℝ) :
    deriv (fun u => a*u^2 + b*u + c) x = 2*a*x + b := by
  have h : (fun u => a*u^2 + b*u + c) =
      fun u => (Polynomial.C a * Polynomial.X^2 + Polynomial.C b * Polynomial.X + Polynomial.C c).eval u := by
    funext u; simp
  rw [h]
  simp only [Polynomial.deriv]
  simp
  ring

private lemma op_1693_noon_witness_loss_monotonicity_one_witness_one_minus_one (q x y : ℝ) :
    noon_realign_witness 1 q x y - 1 =
      2*((q*x)^2 + ((1-q)*y)^2 + 4*(q*x)*((1-q)*y) - (q*x) - ((1-q)*y)) := by
  unfold noon_realign_witness
  simp [Finset.sum_range_succ, Nat.choose]
  ring

private lemma op_1693_noon_witness_loss_monotonicity_one_witness_one_x_deriv (q y x : ℝ) :
    deriv (fun u => noon_realign_witness 1 q u y) x =
      2*q*(2*(q*x) + 4*((1-q)*y) - 1) := by
  have hfun : (fun u => noon_realign_witness 1 q u y) =
      fun u => (2*q^2)*u^2 + (-2*q + 8*q*(1-q)*y)*u + (1 - 2*((1-q)*y) + 2*((1-q)*y)^2) := by
    funext u
    unfold noon_realign_witness
    simp [Finset.sum_range_succ, Nat.choose]
    ring
  rw [hfun]
  rw [op_1693_noon_witness_loss_monotonicity_one_deriv_quadratic]
  ring

private lemma op_1693_noon_witness_loss_monotonicity_one_witness_one_y_deriv (q x y : ℝ) :
    deriv (fun v => noon_realign_witness 1 q x v) y =
      2*(1-q)*(4*(q*x) + 2*((1-q)*y) - 1) := by
  have hfun : (fun v => noon_realign_witness 1 q x v) =
      fun v => (2*(1-q)^2)*v^2 + (-2*(1-q) + 8*(1-q)*q*x)*v + (1 - 2*(q*x) + 2*(q*x)^2) := by
    funext v
    unfold noon_realign_witness
    simp [Finset.sum_range_succ, Nat.choose]
    ring
  rw [hfun]
  rw [op_1693_noon_witness_loss_monotonicity_one_deriv_quadratic]
  ring

private lemma op_1693_noon_witness_loss_monotonicity_one_G_pos_x_bound
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hG : 0 < s^2 + r^2 + 4*s*r - s - r) : 1 ≤ 2*s + 4*r := by
  by_contra h
  push Not at h
  nlinarith [sq_nonneg s, sq_nonneg (r - 1), mul_nonneg hs.le (show (0:ℝ) ≤ 1 - 2*s - 4*r by linarith),
    mul_nonneg hr.le (show (0:ℝ) ≤ 1 - r by linarith)]

private lemma op_1693_noon_witness_loss_monotonicity_one_G_pos_y_bound
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hG : 0 < s^2 + r^2 + 4*s*r - s - r) : 1 ≤ 4*s + 2*r := by
  by_contra h
  push Not at h
  nlinarith [sq_nonneg r, sq_nonneg (s - 1), mul_nonneg hr.le (show (0:ℝ) ≤ 1 - 4*s - 2*r by linarith),
    mul_nonneg hs.le (show (0:ℝ) ≤ 1 - s by linarith)]

private lemma op_1693_noon_witness_loss_monotonicity_one_G_mono
    (s r ds dr : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hds : 0 ≤ ds) (hdr : 0 ≤ dr)
    (hG : 0 < s^2 + r^2 + 4*s*r - s - r) :
    0 < (s+ds)^2 + (r+dr)^2 + 4*(s+ds)*(r+dr) - (s+ds) - (r+dr) := by
  have hA : 0 ≤ 2*s + 4*r - 1 := by
    have := op_1693_noon_witness_loss_monotonicity_one_G_pos_x_bound s r hs hr hG; linarith
  have hB : 0 ≤ 4*s + 2*r - 1 := by
    have := op_1693_noon_witness_loss_monotonicity_one_G_pos_y_bound s r hs hr hG; linarith
  nlinarith [mul_nonneg hA hds, mul_nonneg hB hdr, mul_nonneg hds hdr, sq_nonneg ds, sq_nonneg dr]

/-- For photon number N = 1, whenever W_1 > 1 the partial derivatives are non-negative and the detected region is upward closed. -/
theorem op_1693_noon_witness_loss_monotonicity_one :
    (∀ (q x y : ℝ)
      (hq : q ∈ Set.Ioo 0 1) (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1),
      noon_realign_witness 1 q x y > 1 →
        0 ≤ deriv (fun u => noon_realign_witness 1 q u y) x ∧
        0 ≤ deriv (fun v => noon_realign_witness 1 q x v) y) ∧
    (∀ (q x y x' y' : ℝ)
      (hq : q ∈ Set.Ioo 0 1)
      (hx : 0 < x ∧ x ≤ x' ∧ x' < 1) (hy : 0 < y ∧ y ≤ y' ∧ y' < 1),
      noon_realign_witness 1 q x y > 1 →
        noon_realign_witness 1 q x' y' > 1) := by
  constructor
  · intro q x y hq hx hy hW
    have hqx : 0 < q*x := mul_pos hq.1 hx.1
    have hry : 0 < (1-q)*y := mul_pos (by linarith [hq.2]) hy.1
    have hG : 0 < (q*x)^2 + ((1-q)*y)^2 + 4*(q*x)*((1-q)*y) - (q*x) - ((1-q)*y) := by
      have h := op_1693_noon_witness_loss_monotonicity_one_witness_one_minus_one q x y
      linarith [h, hW]
    have hineq : 1 ≤ 2*(q*x) + 4*((1-q)*y) :=
      op_1693_noon_witness_loss_monotonicity_one_G_pos_x_bound (q*x) ((1-q)*y) hqx hry hG
    have hineq2 : 1 ≤ 4*(q*x) + 2*((1-q)*y) :=
      op_1693_noon_witness_loss_monotonicity_one_G_pos_y_bound (q*x) ((1-q)*y) hqx hry hG
    constructor
    · have hd := op_1693_noon_witness_loss_monotonicity_one_witness_one_x_deriv q y x
      rw [hd]
      nlinarith [hineq, hq.1]
    · have hd := op_1693_noon_witness_loss_monotonicity_one_witness_one_y_deriv q x y
      rw [hd]
      have hq1 : (0:ℝ) < 1 - q := by linarith [hq.2]
      nlinarith [hineq2, hq1]
  · intro q x y x' y' hq hx hy hW
    have hqx : 0 < q*x := mul_pos hq.1 hx.1
    have hry : 0 < (1-q)*y := mul_pos (by linarith [hq.2]) hy.1
    have hG : 0 < (q*x)^2 + ((1-q)*y)^2 + 4*(q*x)*((1-q)*y) - (q*x) - ((1-q)*y) := by
      have h := op_1693_noon_witness_loss_monotonicity_one_witness_one_minus_one q x y
      linarith [h, hW]
    have hds : 0 ≤ q*(x'-x) := mul_nonneg hq.1.le (by linarith [hx.2.1])
    have hdr : 0 ≤ (1-q)*(y'-y) := mul_nonneg (by linarith [hq.2]) (by linarith [hy.2.1])
    have hmono := op_1693_noon_witness_loss_monotonicity_one_G_mono (q*x) ((1-q)*y)
      (q*(x'-x)) ((1-q)*(y'-y)) hqx hry hds hdr hG
    have hx' : q*x + q*(x'-x) = q*x' := by ring
    have hy' : (1-q)*y + (1-q)*(y'-y) = (1-q)*y' := by ring
    rw [hx', hy'] at hmono
    have hW' := op_1693_noon_witness_loss_monotonicity_one_witness_one_minus_one q x' y'
    linarith [hW', hmono]
