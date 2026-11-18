import AFTD.Prelude
import AFTD.Kb.Tcs.Op861FourierCubeIdentity
import AFTD.Kb.Tcs.Op861FourierIndicatorNormIdentity
import AFTD.Kb.Tcs.Op861CubicNormSumBound
import AFTD.Kb.Tcs.Op861OrderThreeCharacterSumBound

/-!
# op861_order_three_zero_sum_upper

Topic: graphs   Node: 8470013a36c5

Provenance: helper lemma. A Fourier upper bound on zero-sum triples, used for op861_ternary_crossing_pairs_dense.

In a finite abelian group where three times every element is zero, for every finite subset S, three times the group order times the number of ordered pairs x,y in S with −x−y in S is at most three times the cube of the size of S plus the group order times (the group order times the size of S minus its square).
-/

open scoped BigOperators
set_option maxHeartbeats 1000000

theorem op861_order_three_zero_sum_upper (G : Type*) [AddCommGroup G]
    [Fintype G] [DecidableEq G] (h3 : ∀ t : G, t+t+t = 0) (S : Finset G) :
    3 * (Fintype.card G : ℝ) *
      (((S.product S).filter (fun xy => -(xy.1+xy.2) ∈ S)).card : ℝ) ≤
      3 * (S.card : ℝ)^3 + (Fintype.card G : ℝ) *
        ((Fintype.card G : ℝ) * S.card - (S.card : ℝ)^2) := by
  classical
  let f : G → ℂ := fun x => if x ∈ S then 1 else 0
  let F : AddChar G ℂ → ℂ := fun χ => ∑ x ∈ S, χ x
  let U : Finset (AddChar G ℂ) := Finset.univ.erase 0
  let T : ℕ := ((S.product S).filter (fun xy => -(xy.1+xy.2) ∈ S)).card
  have hF (χ : AddChar G ℂ) : (∑ x : G, f x * χ x) = F χ := by
    simp [f, F]
  have hF0 : F 0 = (S.card : ℂ) := by simp [F]
  have hne (χ : AddChar G ℂ) (hχ : χ ∈ U) : χ ≠ 0 := by
    exact (Finset.mem_erase.mp hχ).1
  have hnorm : (∑ χ : AddChar G ℂ, ‖F χ‖^2) =
      (Fintype.card G : ℝ) * S.card := by
    simpa [F] using op861_fourier_indicator_norm_identity G S
  have hUsq : (∑ χ ∈ U, ‖F χ‖^2) =
      (Fintype.card G : ℝ) * S.card - (S.card : ℝ)^2 := by
    have hs := Finset.add_sum_erase (Finset.univ : Finset (AddChar G ℂ))
      (fun χ => ‖F χ‖^2) (Finset.mem_univ (0 : AddChar G ℂ))
    rw [← hs] at hnorm
    simp only [hF0, Complex.norm_natCast] at hnorm
    dsimp [U]
    linarith
  have htri : (∑ x : G, ∑ y : G, f x * f y * f (-x-y)) = (T : ℂ) := by
    calc
      _ = ∑ x : G, if x ∈ S then ∑ y ∈ S, f (-x-y) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hmem : x ∈ S
        · simp [f, hmem]
          rw [Finset.natCast_card_filter]
          rw [← Finset.sum_filter]
          simp [Finset.sum_boole]
          congr 1
          ext y
          simp [and_comm]
        · simp [f, hmem]
      _ = ∑ x ∈ S, ∑ y ∈ S, f (-x-y) := by simp
      _ = (T : ℂ) := by
        dsimp [T]
        rw [Finset.natCast_card_filter, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        simp [f, sub_eq_add_neg, neg_add_rev, add_comm]
  have hCube : (S.card : ℂ)^3 + ∑ χ ∈ U, (F χ)^3 =
      (Fintype.card G : ℂ) * T := by
    have hc := op861_fourier_cube_identity G f
    simp_rw [hF] at hc
    rw [htri] at hc
    have hs := Finset.add_sum_erase (Finset.univ : Finset (AddChar G ℂ))
      (fun χ => (F χ)^3) (Finset.mem_univ (0 : AddChar G ℂ))
    rw [← hs, hF0] at hc
    simpa [U] using hc
  have hRe : (∑ χ ∈ U, (F χ)^3).re =
      (Fintype.card G : ℝ) * T - (S.card : ℝ)^3 := by
    have hsimp : ((S.card : ℂ)^3).re = (S.card : ℝ)^3 := by
      change (((S.card : ℝ) : ℂ)^3).re = (S.card : ℝ)^3
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hc := congrArg Complex.re hCube
    simp only [Complex.add_re, hsimp, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at hc
    linarith
  have hbound : 3 * ‖∑ χ ∈ U, (F χ)^3‖ ≤
      (Fintype.card G : ℝ) * ∑ χ ∈ U, ‖F χ‖^2 := by
    apply op861_cubic_norm_sum_bound (AddChar G ℂ) U F (Fintype.card G : ℝ)
    intro χ hχ
    simpa [F] using op861_order_three_character_sum_bound G h3 χ (hne χ hχ) S
  have hR := Complex.re_le_norm (∑ χ ∈ U, (F χ)^3)
  rw [hRe] at hR
  rw [hUsq] at hbound
  change 3 * (Fintype.card G : ℝ) * (T : ℝ) ≤
      3 * (S.card : ℝ)^3 + (Fintype.card G : ℝ) *
        ((Fintype.card G : ℝ) * S.card - (S.card : ℝ)^2)
  nlinarith
