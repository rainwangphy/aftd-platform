import AFTD.Prelude

/-!
# ose_two_layer_direct_embedding

Topic: algorithms   Node: 346edb96e287

Provenance: helper lemma. arXiv:2611.08546, Section 6.1, two-layer cube metric

For two layers over points in an inner-product space, if the first layer is isometric, the cross distances are Euclidean at vertical separation r, and second-layer distances lie between s times and one times the first-layer distances, then the vertical placement of the layers is noncontracting and has Lipschitz constant at most 1/s, for 0<s≤1.
-/

theorem ose_two_layer_direct_embedding (A H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u : A → H) (r s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (M : MetricSpace (Bool × A)) : letI := M; (∀ a b, dist (false,a) (false,b) = dist (u a) (u b)) → (∀ a b, dist (false,a) (true,b)^2 = r^2 + dist (u a) (u b)^2) → (∀ a b, s * dist (u a) (u b) ≤ dist (true,a) (true,b) ∧ dist (true,a) (true,b) ≤ dist (u a) (u b)) → ∃ F : Bool × A → WithLp 2 (H × ℝ), ∀ x y, dist x y ≤ dist (F x) (F y) ∧ dist (F x) (F y) ≤ (1 / s) * dist x y := by
  intro hf hc ht
  let F : Bool × A → WithLp 2 (H × ℝ) := fun p => WithLp.toLp 2 (u p.2, if p.1 then r else 0)
  refine ⟨F, ?_⟩
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hD : 1 ≤ 1 / s := (le_div_iff₀ hs).2 (by linarith)
  have hsq : ∀ b c : Bool, ∀ a d : A,
      dist (F (b,a)) (F (c,d)) ^ 2 = dist (u a) (u d) ^ 2 +
        ((if b then r else 0) - (if c then r else 0)) ^ 2 := by
    intro b c a d
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
    simp [F, dist_eq_norm, Real.norm_eq_abs, sq_abs]
  intro ⟨b,a⟩ ⟨c,d⟩
  cases b <;> cases c
  · have he := hsq false false a d
    simp only [Bool.false_eq_true, ↓reduceIte, sub_self, zero_pow, add_zero] at he
    have heq : dist (F (false,a)) (F (false,d)) = dist (u a) (u d) := by
      nlinarith [dist_nonneg (x := F (false,a)) (y := F (false,d)), dist_nonneg (x := u a) (y := u d)]
    rw [hf, heq]
    exact ⟨le_refl _, le_mul_of_one_le_left dist_nonneg hD⟩
  · have he := hsq false true a d
    simp only [Bool.false_eq_true, ↓reduceIte, zero_sub, neg_sq] at he
    have hm := hc a d
    have heq : dist (F (false,a)) (F (true,d)) = dist (false,a) (true,d) := by
      nlinarith [dist_nonneg (x := F (false,a)) (y := F (true,d)), dist_nonneg (x := (false,a)) (y := (true,d))]
    rw [heq]
    exact ⟨le_refl _, le_mul_of_one_le_left dist_nonneg hD⟩
  · have he := hsq true false a d
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at he
    have hm := hc d a
    rw [dist_comm (false,d) (true,a), dist_comm (u d) (u a)] at hm
    have heq : dist (F (true,a)) (F (false,d)) = dist (true,a) (false,d) := by
      nlinarith [dist_nonneg (x := F (true,a)) (y := F (false,d)), dist_nonneg (x := (true,a)) (y := (false,d))]
    rw [heq]
    exact ⟨le_refl _, le_mul_of_one_le_left dist_nonneg hD⟩
  · have he := hsq true true a d
    simp only [↓reduceIte, sub_self, zero_pow, add_zero] at he
    have heq : dist (F (true,a)) (F (true,d)) = dist (u a) (u d) := by
      nlinarith [dist_nonneg (x := F (true,a)) (y := F (true,d)), dist_nonneg (x := u a) (y := u d)]
    rw [heq]
    refine ⟨(ht a d).2, ?_⟩
    have h := (ht a d).1
    rw [one_div, ← div_eq_inv_mul]
    exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using h)
