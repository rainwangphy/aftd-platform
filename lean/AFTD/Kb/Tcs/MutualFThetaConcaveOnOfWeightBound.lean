import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFTheta
import AFTD.Kb.Tcs.SubadditiveFWeight
import AFTD.Kb.Tcs.SubadditiveGenVariance
import AFTD.Kb.Tcs.ProbSimplexConcaveOnOfHasDerivAt2
import AFTD.Kb.Tcs.PerspectiveAffineHasDerivAtZero
import AFTD.Kb.Tcs.HasDerivAtCompAffineAtZero
import AFTD.Kb.Tcs.PerspectiveAffineDerivHasDerivAtZero
import AFTD.Kb.Tcs.SubadditiveGenVarianceConcaveOn
import AFTD.Kb.Tcs.SubadditiveFWeightHasDerivAtFacts

/-!
# mutual_f_theta_concaveOn_of_weight_bound

Topic: information   Node: 16cde58afc05

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, Lemma 4

Lemma 4 of arXiv:2610.21231: under the assumptions of Theorem 1 (g = x² f'' with g'' < 0 and g + 2(g' - η)²/(-g'') ≤ 2η + (x-1)ℓ), for full-support p_X and p_{Y|X}, r_X ↦ Θ_{p_X,p_{Y|X}}(r_X) is concave on the open probability simplex.
-/

theorem mutual_f_theta_concaveOn_of_weight_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (f : ℝ → ℝ) (hf1 : f 1 = 0) (hconv : ConvexOn ℝ (Set.Ioi 0) f)
    (hsmooth : ContDiffOn ℝ 4 f (Set.Ioi 0))
    (hg2 : ∀ x > 0, deriv (deriv (subadditive_f_weight f)) x < 0)
    (hbound : ∃ η ℓ : ℝ, 0 < η ∧ ∀ x > 0,
      subadditive_f_weight f x + 2 * (deriv (subadditive_f_weight f) x - η) ^ 2 /
        (-deriv (deriv (subadditive_f_weight f)) x) ≤ 2 * η + (x - 1) * ℓ)
    (pX : X → ℝ) (PY : X → Y → ℝ) (hpX : ∀ x, 0 < pX x) (hsX : ∑ x, pX x = 1)
    (hPY : ∀ x y, 0 < PY x y) (hsY : ∀ x, ∑ y, PY x y = 1) :
    ConcaveOn ℝ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} (mutual_f_theta f pX PY) := by
  classical
  obtain ⟨η, ℓ, _, hb⟩ := hbound
  have hfacts := subadditive_f_weight_hasDerivAt_facts f hsmooth
  set f1 := deriv f
  set f2 := deriv (deriv f)
  set gw := subadditive_f_weight f
  have hgdef : ∀ a, gw a = a ^ 2 * f2 a := fun a => rfl
  have hcc := subadditive_gen_variance_concaveOn (X := X) gw (deriv gw) (deriv (deriv gw))
    (fun a ha => (hfacts a ha).2.2.1) (fun a ha => (hfacts a ha).2.2.2) hg2 η ℓ hb
  let D1 : (X → ℝ) → (X → ℝ) → ℝ := fun r v =>
    ∑ y, ∑ x, pX x * ((∑ x', v x' * PY x' y) * f (r x * PY x y / pX x / ∑ x', r x' * PY x' y) +
      (v x * PY x y / pX x * (∑ x', r x' * PY x' y) - r x * PY x y / pX x * (∑ x', v x' * PY x' y)) *
        f1 (r x * PY x y / pX x / ∑ x', r x' * PY x' y) / (∑ x', r x' * PY x' y)) -
    ∑ x, pX x * (f1 (r x / pX x) * (v x / pX x))
  let D2 : (X → ℝ) → (X → ℝ) → ℝ := fun r v =>
    ∑ y, ∑ x, pX x * ((v x * PY x y / pX x * (∑ x', r x' * PY x' y) -
        r x * PY x y / pX x * (∑ x', v x' * PY x' y)) ^ 2 *
        f2 (r x * PY x y / pX x / ∑ x', r x' * PY x' y) / (∑ x', r x' * PY x' y) ^ 3) -
    ∑ x, pX x * (f2 (r x / pX x) * (v x / pX x) * (v x / pX x))
  have hlin : ∀ (r v : X → ℝ) (t : ℝ) (y : Y),
      ∑ x', (r + t • v) x' * PY x' y = ∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y := by
    intro r v t y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have hQpos : ∀ r : X → ℝ, (∀ x, 0 < r x) → ∑ x, r x = 1 → ∀ y, 0 < ∑ x', r x' * PY x' y := by
    intro r hr hs y
    have hX : Nonempty X := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hs
    exact Finset.sum_pos (fun x _ => mul_pos (hr x) (hPY x y))
      ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  apply prob_simplex_concaveOn_of_hasDerivAt2 (mutual_f_theta f pX PY) D1 D2
  · intro r hr hs v _
    have hfun : (fun t : ℝ => mutual_f_theta f pX PY (r + t • v)) = fun t : ℝ =>
        ∑ y, ∑ x, pX x * ((∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y) *
          f ((r x * PY x y / pX x + t * (v x * PY x y / pX x)) /
            (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y))) -
        ∑ x, pX x * f (r x / pX x + t * (v x / pX x)) := by
      funext t
      simp only [mutual_f_theta, hlin]
      congr 1
      · refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show (r x + t * v x) * PY x y / (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y) /
            pX x = (r x * PY x y / pX x + t * (v x * PY x y / pX x)) /
            (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y) by ring]
        ring
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show (r x + t * v x) / pX x = r x / pX x + t * (v x / pX x) by ring]
    rw [hfun]
    refine HasDerivAt.fun_sub (HasDerivAt.fun_sum (fun y _ => HasDerivAt.fun_sum (fun x _ => ?_)))
      (HasDerivAt.fun_sum (fun x _ => ?_))
    · have hu : 0 < r x * PY x y / pX x / ∑ x', r x' * PY x' y :=
        div_pos (div_pos (mul_pos (hr x) (hPY x y)) (hpX x)) (hQpos r hr hs y)
      exact (perspective_affine_hasDerivAt_zero f f1 _ (∑ x', v x' * PY x' y) _ (v x * PY x y / pX x) (hQpos r hr hs y) (hfacts _ hu).1).const_mul (pX x)
    · exact (hasDerivAt_comp_affine_at_zero f _ _ (v x / pX x)
        (hfacts _ (div_pos (hr x) (hpX x))).1).const_mul (pX x)
  · intro r hr hs v _
    have hfun : (fun t : ℝ => D1 (r + t • v) v) = fun t : ℝ =>
        ∑ y, ∑ x, pX x * ((∑ x', v x' * PY x' y) *
          f ((r x * PY x y / pX x + t * (v x * PY x y / pX x)) /
            (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y)) +
          (v x * PY x y / pX x * (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y) -
            (r x * PY x y / pX x + t * (v x * PY x y / pX x)) * (∑ x', v x' * PY x' y)) *
          f1 ((r x * PY x y / pX x + t * (v x * PY x y / pX x)) /
            (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y)) /
          (∑ x', r x' * PY x' y + t * ∑ x', v x' * PY x' y)) -
        ∑ x, pX x * (f1 (r x / pX x + t * (v x / pX x)) * (v x / pX x)) := by
      funext t
      have e1 : ∀ x y, (r + t • v) x * PY x y / pX x =
          r x * PY x y / pX x + t * (v x * PY x y / pX x) := by
        intro x y; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have e2 : ∀ x, (r + t • v) x / pX x = r x / pX x + t * (v x / pX x) := by
        intro x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      simp only [D1, hlin, e1, e2]
    rw [hfun]
    refine HasDerivAt.fun_sub (HasDerivAt.fun_sum (fun y _ => HasDerivAt.fun_sum (fun x _ => ?_)))
      (HasDerivAt.fun_sum (fun x _ => ?_))
    · have hu : 0 < r x * PY x y / pX x / ∑ x', r x' * PY x' y :=
        div_pos (div_pos (mul_pos (hr x) (hPY x y)) (hpX x)) (hQpos r hr hs y)
      exact (perspective_affine_deriv_hasDerivAt_zero f f1 f2 _ (∑ x', v x' * PY x' y) _ (v x * PY x y / pX x) (hQpos r hr hs y) (hfacts _ hu).1
        (hfacts _ hu).2.1).const_mul (pX x)
    · exact ((hasDerivAt_comp_affine_at_zero f1 _ _ (v x / pX x)
        (hfacts _ (div_pos (hr x) (hpX x))).2.1).mul_const (v x / pX x)).const_mul (pX x)
  · intro r hr hs v hv
    set Q : Y → ℝ := fun y => ∑ x', r x' * PY x' y with hQ
    set W : Y → ℝ := fun y => ∑ x', v x' * PY x' y with hW
    set β : X → ℝ := fun x => v x / r x with hβ
    set ry : Y → X → ℝ := fun y x => r x * PY x y / Q y with hry
    have hQp : ∀ y, 0 < Q y := hQpos r hr hs
    have hmem : ∀ y ∈ (Finset.univ : Finset Y),
        ry y ∈ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} := by
      intro y _
      refine ⟨fun x => div_pos (mul_pos (hr x) (hPY x y)) (hQp y), ?_⟩
      simp only [hry, ← Finset.sum_div]
      exact div_self (hQp y).ne'
    have hsQ : ∑ y, Q y = 1 := by
      simp only [hQ]; rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hsY, mul_one, hs]
    have hsum : ∑ y, Q y • ry y = r := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hry]
      have : ∀ y, Q y * (r x * PY x y / Q y) = r x * PY x y := fun y =>
        mul_div_cancel₀ _ (hQp y).ne'
      simp only [this, ← Finset.mul_sum, hsY, mul_one]
    have hj := (hcc pX β hpX hsX).le_map_sum (t := Finset.univ) (w := Q) (p := ry)
      (fun y _ => (hQp y).le) hsQ hmem
    rw [hsum] at hj
    simp only [smul_eq_mul] at hj
    have hmy : ∀ y, ∑ x', ry y x' * β x' = W y / Q y := by
      intro y
      simp only [hry, hβ, hW]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have := (hr x).ne'
      field_simp
    have hm0 : ∑ x', r x' * β x' = 0 := by
      simp only [hβ]
      rw [← hv]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have := (hr x).ne'
      field_simp
    have hD2 : D2 r v = ∑ y, Q y * subadditive_gen_variance gw pX β (ry y) - subadditive_gen_variance gw pX β r := by
      simp only [D2, subadditive_gen_variance, hmy, hm0]
      congr 1
      · refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [hry, hgdef, hQ, hW, hβ]
        have hp := (hpX x).ne'
        have hq : (∑ x', r x' * PY x' y) ≠ 0 := (hQpos r hr hs y).ne'
        have hrx := (hr x).ne'
        rw [show r x * PY x y / (∑ x', r x' * PY x' y) / pX x =
          r x * PY x y / pX x / (∑ x', r x' * PY x' y) by ring]
        field_simp
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [hgdef, hβ]
        have hp := (hpX x).ne'
        have hrx := (hr x).ne'
        field_simp
        ring
    rw [hD2]
    linarith
