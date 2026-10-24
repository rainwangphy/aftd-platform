import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveGenVariance
import AFTD.Kb.Tcs.ProbSimplexConcaveOnOfHasDerivAt2
import AFTD.Kb.Tcs.HasDerivAtCompAffineAtZero

/-!
# subadditive_gen_variance_concaveOn

Topic: information   Node: ca4f3b2b2e65

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Lemma 4

Inner step of Lemma 4 of arXiv:2610.21231: if g'' < 0 on (0, ∞) and g + 2(g' - η)²/(-g'') ≤ 2η + (x - 1)ℓ there, then for full-support p_X and any u, q ↦ E_p[g(q/p)(u - E_q u)²] is concave on the open probability simplex.
-/

theorem subadditive_gen_variance_concaveOn {X : Type*} [Fintype X] (gw g1 g2 : ℝ → ℝ)
    (hd1 : ∀ a > 0, HasDerivAt gw (g1 a) a) (hd2 : ∀ a > 0, HasDerivAt g1 (g2 a) a)
    (hg2 : ∀ a > 0, g2 a < 0) (η ℓ : ℝ)
    (hb : ∀ a > 0, gw a + 2 * (g1 a - η) ^ 2 / (-g2 a) ≤ 2 * η + (a - 1) * ℓ)
    (pX u : X → ℝ) (hpX : ∀ x, 0 < pX x) (hsX : ∑ x, pX x = 1) :
    ConcaveOn ℝ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} (subadditive_gen_variance gw pX u) := by
  classical
  let D1 : (X → ℝ) → (X → ℝ) → ℝ := fun s k =>
    ∑ x, pX x * (g1 (s x / pX x) * (k x / pX x) * (u x - ∑ x', s x' * u x') ^ 2 +
      gw (s x / pX x) * (2 * (u x - ∑ x', s x' * u x') * -(∑ x', k x' * u x')))
  let D2 : (X → ℝ) → (X → ℝ) → ℝ := fun s k =>
    ∑ x, pX x * (g2 (s x / pX x) * (k x / pX x) * (k x / pX x) * (u x - ∑ x', s x' * u x') ^ 2 +
      g1 (s x / pX x) * (k x / pX x) * (2 * (u x - ∑ x', s x' * u x') * -(∑ x', k x' * u x')) +
      (g1 (s x / pX x) * (k x / pX x) * (2 * (u x - ∑ x', s x' * u x') * -(∑ x', k x' * u x')) +
        gw (s x / pX x) * (2 * -(∑ x', k x' * u x') * -(∑ x', k x' * u x'))))
  have hlin : ∀ (s k : X → ℝ) (t : ℝ),
      ∑ x', (s + t • k) x' * u x' = ∑ x', s x' * u x' + t * ∑ x', k x' * u x' := by
    intro s k t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have harg : ∀ (s k : X → ℝ) (t : ℝ) (x : X),
      (s + t • k) x / pX x = s x / pX x + t * (k x / pX x) := by
    intro s k t x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  apply prob_simplex_concaveOn_of_hasDerivAt2 (subadditive_gen_variance gw pX u) D1 D2
  · intro s hs _ k _
    have hpos : ∀ x, 0 < s x / pX x := fun x => div_pos (hs x) (hpX x)
    have hfun : (fun t : ℝ => subadditive_gen_variance gw pX u (s + t • k)) = fun t : ℝ =>
        ∑ x, pX x * gw (s x / pX x + t * (k x / pX x)) *
          (u x - (∑ x', s x' * u x' + t * ∑ x', k x' * u x')) ^ 2 := by
      funext t; simp only [subadditive_gen_variance, hlin, harg]
    rw [hfun]
    refine HasDerivAt.fun_sum (fun x _ => ?_)
    have hG := hasDerivAt_comp_affine_at_zero gw _ _ (k x / pX x) (hd1 _ (hpos x))
    have hD : HasDerivAt (fun t : ℝ => u x - (∑ x', s x' * u x' + t * ∑ x', k x' * u x'))
        (-(∑ x', k x' * u x')) 0 := by
      simpa using (((hasDerivAt_id' (0:ℝ)).mul_const (∑ x', k x' * u x')).const_add
        (∑ x', s x' * u x')).const_sub (u x)
    have := ((hG.const_mul (pX x)).fun_mul (hD.fun_pow 2))
    exact this.congr_deriv (by norm_num <;> ring)
  · intro s hs _ k _
    have hpos : ∀ x, 0 < s x / pX x := fun x => div_pos (hs x) (hpX x)
    have hfun : (fun t : ℝ => D1 (s + t • k) k) = fun t : ℝ =>
        ∑ x, pX x * (g1 (s x / pX x + t * (k x / pX x)) * (k x / pX x) *
          (u x - (∑ x', s x' * u x' + t * ∑ x', k x' * u x')) ^ 2 +
          gw (s x / pX x + t * (k x / pX x)) *
            (2 * (u x - (∑ x', s x' * u x' + t * ∑ x', k x' * u x')) * -(∑ x', k x' * u x'))) := by
      funext t; simp only [D1, hlin, harg]
    rw [hfun]
    refine HasDerivAt.fun_sum (fun x _ => ?_)
    have hG := hasDerivAt_comp_affine_at_zero gw _ _ (k x / pX x) (hd1 _ (hpos x))
    have hG1 := hasDerivAt_comp_affine_at_zero g1 _ _ (k x / pX x) (hd2 _ (hpos x))
    have hD : HasDerivAt (fun t : ℝ => u x - (∑ x', s x' * u x' + t * ∑ x', k x' * u x'))
        (-(∑ x', k x' * u x')) 0 := by
      simpa using (((hasDerivAt_id' (0:ℝ)).mul_const (∑ x', k x' * u x')).const_add
        (∑ x', s x' * u x')).const_sub (u x)
    have := (((hG1.mul_const (k x / pX x)).fun_mul (hD.fun_pow 2)).add
      (hG.fun_mul ((hD.const_mul 2).mul_const (-(∑ x', k x' * u x'))))).const_mul (pX x)
    exact this.congr_deriv (by norm_num <;> ring)
  · intro s hs hs1 k hk
    set m := ∑ x', s x' * u x' with hm
    set κ := ∑ x', k x' * u x' with hκ
    have hterm : ∀ x, pX x * (g2 (s x / pX x) * (k x / pX x) * (k x / pX x) * (u x - m) ^ 2 +
        g1 (s x / pX x) * (k x / pX x) * (2 * (u x - m) * -κ) +
        (g1 (s x / pX x) * (k x / pX x) * (2 * (u x - m) * -κ) +
          gw (s x / pX x) * (2 * -κ * -κ))) ≤
        4 * η * κ ^ 2 * pX x + 2 * κ ^ 2 * ℓ * s x - 2 * κ ^ 2 * ℓ * pX x -
          4 * η * κ * (k x * u x) + 4 * η * κ * m * k x := by
      intro x
      have hp := hpX x
      have ha : 0 < s x / pX x := div_pos (hs x) hp
      set a := s x / pX x with hadef
      set b := k x / pX x with hbdef
      set d := u x - m with hd
      set Gv2 := g2 a
      set Gv1 := g1 a
      set Gv := gw a
      have hG2 : Gv2 < 0 := hg2 a ha
      have hq : 0 ≤ 4 * κ ^ 2 * (Gv1 - η) ^ 2 / (-Gv2) - ((b * d) ^ 2 * Gv2 - 4 * (b * d) * κ * (Gv1 - η)) := by
        have : 4 * κ ^ 2 * (Gv1 - η) ^ 2 / (-Gv2) - ((b * d) ^ 2 * Gv2 - 4 * (b * d) * κ * (Gv1 - η)) =
            ((b * d) * Gv2 - 2 * κ * (Gv1 - η)) ^ 2 / (-Gv2) := by
          have h1 : Gv2 ≠ 0 := hG2.ne
          have h2 : -Gv2 ≠ 0 := by linarith
          field_simp; ring
        rw [this]; exact div_nonneg (sq_nonneg _) (by linarith)
      have hbb := hb a ha
      have hR : 4 * κ ^ 2 * (Gv1 - η) ^ 2 / (-Gv2) = 2 * κ ^ 2 * (2 * (Gv1 - η) ^ 2 / (-Gv2)) := by ring
      have hT : (b * d) ^ 2 * Gv2 - 4 * (b * d) * κ * Gv1 + 2 * κ ^ 2 * Gv ≤
          2 * κ ^ 2 * (2 * η + (a - 1) * ℓ) - 4 * (b * d) * κ * η := by
        have h2 : 2 * κ ^ 2 * (Gv + 2 * (Gv1 - η) ^ 2 / (-Gv2)) ≤ 2 * κ ^ 2 * (2 * η + (a - 1) * ℓ) :=
          mul_le_mul_of_nonneg_left hbb (by positivity)
        nlinarith [hq, hR, h2]
      have hpb : pX x * b = k x := by rw [hbdef]; field_simp
      have hpa : pX x * a = s x := by rw [hadef]; field_simp
      have := mul_le_mul_of_nonneg_left hT hp.le
      have e1 : pX x * (Gv2 * b * b * d ^ 2 + Gv1 * b * (2 * d * -κ) + (Gv1 * b * (2 * d * -κ) + Gv * (2 * -κ * -κ))) =
          pX x * ((b * d) ^ 2 * Gv2 - 4 * (b * d) * κ * Gv1 + 2 * κ ^ 2 * Gv) := by ring
      have e2 : pX x * (2 * κ ^ 2 * (2 * η + (a - 1) * ℓ) - 4 * (b * d) * κ * η) =
          4 * η * κ ^ 2 * pX x + 2 * κ ^ 2 * ℓ * (pX x * a) - 2 * κ ^ 2 * ℓ * pX x -
            4 * η * κ * ((pX x * b) * d) := by ring
      rw [e1]
      rw [e2, hpb, hpa] at this
      rw [hd] at this
      linarith
    calc D2 s k ≤ ∑ x, (4 * η * κ ^ 2 * pX x + 2 * κ ^ 2 * ℓ * s x - 2 * κ ^ 2 * ℓ * pX x -
          4 * η * κ * (k x * u x) + 4 * η * κ * m * k x) := Finset.sum_le_sum (fun x _ => hterm x)
      _ = 4 * η * κ ^ 2 * ∑ x, pX x + 2 * κ ^ 2 * ℓ * ∑ x, s x - 2 * κ ^ 2 * ℓ * ∑ x, pX x -
          4 * η * κ * κ + 4 * η * κ * m * ∑ x, k x := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hκ]
      _ = 0 := by rw [hsX, hs1, hk]; ring
