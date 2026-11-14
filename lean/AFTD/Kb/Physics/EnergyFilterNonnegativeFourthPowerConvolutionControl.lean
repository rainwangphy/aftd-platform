import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFiniteYoungSquareEstimate

/-!
# energy_filter_nonnegative_fourth_power_convolution_control

Topic: statistical_mechanics   Node: a82e04a8fcc3

Provenance: helper lemma. OP-892: convolution and quartic-cycle summability.

For a nonnegative real integer sequence u with summable fourth powers, each convolution of u³ with itself is summable and the squares of those convolution sums are summable.
-/

theorem energy_filter_nonnegative_fourth_power_convolution_control
    (u : ℤ → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu : Summable (fun i => u i ^ 4)) :
    (∀ m : ℤ, Summable (fun j : ℤ => u j ^ 3 * u (m-j) ^ 3)) ∧
    Summable (fun m : ℤ => (∑' j : ℤ, u j ^ 3 * u (m-j) ^ 3)^2) := by
  let f : ℤ → ℝ := fun i => u i ^ 4
  let U : ℝ := ∑' i, f i
  have hf : Summable f := hu
  have hf0 (i : ℤ) : 0 ≤ f i := by dsimp [f]; positivity
  have hU : 0 ≤ U := tsum_nonneg hf0
  have hfU (i : ℤ) : f i ≤ U := hf.le_tsum i (fun j hj => hf0 j)
  have hfnorm : Summable (fun i => ‖f i‖) := by simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hf
  have hprod : Summable (fun p : ℤ × ℤ => f p.1 * f p.2) :=
    summable_mul_of_summable_norm hfnorm hfnorm
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) := {
    toFun := fun p => (p.2, p.1-p.2)
    invFun := fun p => (p.1+p.2, p.1)
    left_inv := by intro p; rcases p with ⟨m,j⟩; simp
    right_inv := by intro p; rcases p with ⟨j,l⟩; simp }
  have hpair : Summable (fun p : ℤ × ℤ => f p.2 * f (p.1-p.2)) := by
    simpa [Function.comp_def,e] using (e.summable_iff).2 hprod
  have hB : Summable (fun m : ℤ => ∑' j : ℤ, f j * f (m-j)) := by
    have hp := (summable_prod_of_nonneg (show 0 ≤ (fun p : ℤ × ℤ => f p.2 * f (p.1-p.2)) from
      fun p => mul_nonneg (hf0 _) (hf0 _))).1 hpair
    exact hp.2
  have hBsum (m : ℤ) : Summable (fun j : ℤ => f j * f (m-j)) := hpair.prod_factor m
  have hBbound (m : ℤ) : (∑' j : ℤ, f j*f (m-j)) ≤ U*U := by
    calc
      _ ≤ ∑' j : ℤ, f j * U :=
        Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hfU (m-j)) (hf0 j))
          (hBsum m) (hf.mul_right U)
      _ = U*U := by rw [hf.tsum_mul_right]
  have hshift (m : ℤ) : Summable (fun j : ℤ => f (m-j)) := by
    let eqv : ℤ ≃ ℤ := {
      toFun := fun j => m-j
      invFun := fun j => m-j
      left_inv := by intro j; dsimp; omega
      right_inv := by intro j; dsimp; omega }
    simpa [Function.comp_def,eqv] using (eqv.summable_iff).2 hf
  have hshift_sum (m : ℤ) : (∑' j : ℤ, f (m-j)) = U := by
    let eqv : ℤ ≃ ℤ := {
      toFun := fun j => m-j
      invFun := fun j => m-j
      left_inv := by intro j; dsimp; omega
      right_inv := by intro j; dsimp; omega }
    simpa [eqv,U] using eqv.tsum_eq f
  have hsums (m : ℤ) (s : Finset ℤ) :
      (∑ j ∈ s, u j ^ 3 * u (m-j) ^ 3)^2 ≤ U * (∑ j ∈ s, f j * f (m-j)) := by
    apply energy_filter_finite_young_square_estimate s u (fun j => u (m-j)) U hU
    · exact hf.sum_le_tsum s (fun j hj => hf0 j)
    · have hh := (hshift m).sum_le_tsum s (fun j hj => hf0 (m-j))
      rwa [hshift_sum] at hh
  have hAsum (m : ℤ) : Summable (fun j : ℤ => u j ^ 3 * u (m-j) ^ 3) := by
    apply summable_of_sum_le (show 0 ≤ (fun j : ℤ => u j ^ 3 * u (m-j) ^ 3) from
      fun j => mul_nonneg (pow_nonneg (hu0 j) _) (pow_nonneg (hu0 (m-j)) _))
      (c := U*(U*U)+1)
    intro s
    have hb : (∑ j ∈ s, f j*f (m-j)) ≤ U*U :=
      ((hBsum m).sum_le_tsum s (fun j hj => mul_nonneg (hf0 j) (hf0 _))).trans (hBbound m)
    have hs := hsums m s
    have hmul := mul_le_mul_of_nonneg_left hb hU
    have hsimple : (∑ j ∈ s, u j ^ 3 * u (m-j) ^ 3) ≤
        (∑ j ∈ s, u j ^ 3 * u (m-j) ^ 3)^2 + 1 := by
      nlinarith [sq_nonneg ((∑ j ∈ s, u j ^ 3 * u (m-j) ^ 3) - 1/2)]
    linarith
  have hbound (m : ℤ) : (∑' j : ℤ, u j ^ 3 * u (m-j) ^ 3)^2 ≤
      U * (∑' j : ℤ, f j*f (m-j)) := by
    apply le_of_tendsto_of_tendsto ((hAsum m).hasSum.pow 2)
      (tendsto_const_nhds.mul (hBsum m).hasSum)
    exact Filter.Eventually.of_forall (hsums m)
  refine ⟨hAsum, ?_⟩
  apply (hB.mul_left U).of_nonneg_of_le
  · intro m; exact sq_nonneg _
  · intro m; exact hbound m
