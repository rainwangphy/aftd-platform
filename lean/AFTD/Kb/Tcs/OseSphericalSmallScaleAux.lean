import AFTD.Prelude

/-!
# ose_spherical_small_scale_aux

Topic: algorithms   Node: 32e40b5d425d

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; small-scale spherical two-layer construction

For two spherical metric layers satisfying the displayed scalar inequalities and the two-scale norm identity, if the first-layer metric is the original inner-product metric, the cross-layer squared distances are r² plus its square, and the second-layer distances are s times its square, then both layers admit a noncontracting Hilbert-product embedding with Lipschitz constant q.
-/

theorem ose_spherical_small_scale_aux (A H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : A → H) (c : H) (q r s β : ℝ)
    (hq : 1 ≤ q) (hr : 0 ≤ r) (hs : 0 < s) (hsmall : s*q ≤ 1)
    (hβ1 : 1 ≤ β) (hβq : β ≤ q) (hprod : (s*q)*β ≤ 1)
    (hdiff : (β-s*q)^2 ≤ 4*r^2)
    (hparam : r^2 + q^2 * (1 - (s*q)*β) ≤ q^2 * r^2)
    (hu : ∀ a, ‖u a-c‖^2 = q^2/4)
    (hsep : ∀ a b, a ≠ b → 1 ≤ dist (u a) (u b))
    (hidentity : ∀ (x y : H), ‖x‖^2=q^2/4 → ‖y‖^2=q^2/4 →
      ‖β • x - (s*q) • y‖^2 = (β-s*q)^2*q^2/4 + (s*q)*β*‖x-y‖^2)
    (M : MetricSpace (Bool × A)) : letI := M
    (∀ a b, dist (false,a) (false,b) = dist (u a) (u b)) →
    (∀ a b, dist (false,a) (true,b)^2 = r^2 + dist (u a) (u b)^2) →
    (∀ a b, dist (true,a) (true,b) = s * dist (u a) (u b)^2) →
    ∃ F : Bool × A → WithLp 2 (H × ℝ),
      ∀ x y, dist x y ≤ dist (F x) (F y) ∧ dist (F x) (F y) ≤ q * dist x y := by
  intro hf hc ht
  let α := s*q
  let C := (β-α)^2*q^2/4
  let z := max 0 (r^2+q^2*(1-α*β)-C)
  have hq0 : 0 ≤ q := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hz0 : 0 ≤ z := le_max_left _ _
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCla : C ≤ q^2*r^2 := by
    have hmul := mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hdiff)
    dsimp [C,α] at *
    nlinarith
  have hbaseLo : r^2+q^2*(1-α*β) ≤ C+z := by
    have hz := le_max_right (0 : ℝ) (r^2+q^2*(1-α*β)-C)
    dsimp [z]; linarith
  have hbaseHi : C+z ≤ q^2*r^2 := by
    have hz : z ≤ q^2*r^2-C := by
      dsimp [z]
      apply max_le
      · linarith
      · dsimp [α] at *
        linarith
    linarith
  have hnorm (a : A) : ‖u a-c‖ = q/2 := by
    have h := hu a
    have hn : 0 ≤ ‖u a-c‖ := norm_nonneg _
    nlinarith
  have hdiam (a b : A) : dist (u a) (u b) ≤ q := by
    have htri := dist_triangle (u a) c (u b)
    have h1 : dist (u a) c = q/2 := by rw [dist_eq_norm, hnorm]
    have h2 : dist c (u b) = q/2 := by rw [dist_comm, dist_eq_norm, hnorm]
    linarith
  let T : Bool → ℝ := fun b => if b then α else β
  let Z : Bool → ℝ := fun b => if b then Real.sqrt z else 0
  let F : Bool × A → WithLp 2 (H × ℝ) := fun p => WithLp.toLp 2 (T p.1 • (u p.2-c), Z p.1)
  have hFsq (b1 b2 : Bool) (a1 a2 : A) :
      dist (F (b1,a1)) (F (b2,a2))^2 =
      ‖T b1 • (u a1-c) - T b2 • (u a2-c)‖^2 + (Z b1-Z b2)^2 := by
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
    simp [F, WithLp.sub_fst, WithLp.sub_snd, Real.norm_eq_abs, sq_abs]
  have hcrossout (a b : A) :
      dist (F (false,a)) (F (true,b))^2 = C+z+(α*β)*dist (u a) (u b)^2 := by
    rw [hFsq]
    simp only [T, Z, Bool.false_eq_true, ↓reduceIte, zero_sub, neg_sq, Real.sq_sqrt hz0]
    rw [hidentity (u a-c) (u b-c) (hu a) (hu b)]
    have hsub : ‖(u a-c)-(u b-c)‖ = dist (u a) (u b) := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [hsub]
    dsimp [C,α]
    ring
  refine ⟨F, ?_⟩
  intro ⟨b1,a⟩ ⟨b2,b⟩
  cases b1 <;> cases b2
  · have he := hFsq false false a b
    simp only [T,Z,Bool.false_eq_true,↓reduceIte,sub_self,zero_pow,add_zero] at he
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0, mul_pow] at he
    have hd : ‖(u a-c)-(u b-c)‖ = dist (u a) (u b) := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [hd] at he
    have hx := hf a b
    have hfa : 0 ≤ dist (F (false,a)) (F (false,b)) := dist_nonneg
    have hda : 0 ≤ dist (u a) (u b) := dist_nonneg
    have hβδ : 0 ≤ β * dist (u a) (u b) := mul_nonneg hβ0 hda
    have heq : dist (F (false,a)) (F (false,b)) = β * dist (u a) (u b) := by nlinarith
    rw [hx,heq]
    exact ⟨le_mul_of_one_le_left hda hβ1, mul_le_mul_of_nonneg_right hβq hda⟩
  · have he := hcrossout a b
    have hx := hc a b
    have hδ0 : 0 ≤ dist (u a) (u b) := dist_nonneg
    have hδq := hdiam a b
    have hk0 : 0 ≤ α*β := mul_nonneg hα0 hβ0
    have hk1 : α*β ≤ 1 := hprod
    have h1 := mul_nonneg (show 0 ≤ 1-α*β by linarith)
      (show 0 ≤ q^2-dist (u a) (u b)^2 by nlinarith)
    have h2 := mul_nonneg (show 0 ≤ q^2-α*β by nlinarith) (sq_nonneg (dist (u a) (u b)))
    have hlow : dist (false,a) (true,b)^2 ≤ dist (F (false,a)) (F (true,b))^2 := by
      nlinarith [hbaseLo,h1]
    have hxq := congrArg (fun t : ℝ => q^2 * t) hx
    have hhigh : dist (F (false,a)) (F (true,b))^2 ≤ (q*dist (false,a) (true,b))^2 := by
      nlinarith [hbaseHi,h2,hxq]
    constructor
    · exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg (by norm_num : 2 ≠ 0)).1 hlow
    · exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg hq0 dist_nonneg) (by norm_num : 2 ≠ 0)).1 hhigh
  · rw [dist_comm (true,a) (false,b), dist_comm (F (true,a)) (F (false,b))]
    have he := hcrossout b a
    have hx := hc b a
    have hδ0 : 0 ≤ dist (u b) (u a) := dist_nonneg
    have hδq := hdiam b a
    have hk0 : 0 ≤ α*β := mul_nonneg hα0 hβ0
    have hk1 : α*β ≤ 1 := hprod
    have h1 := mul_nonneg (show 0 ≤ 1-α*β by linarith)
      (show 0 ≤ q^2-dist (u b) (u a)^2 by nlinarith)
    have h2 := mul_nonneg (show 0 ≤ q^2-α*β by nlinarith) (sq_nonneg (dist (u b) (u a)))
    have hlow : dist (false,b) (true,a)^2 ≤ dist (F (false,b)) (F (true,a))^2 := by
      nlinarith [hbaseLo,h1]
    have hxq := congrArg (fun t : ℝ => q^2 * t) hx
    have hhigh : dist (F (false,b)) (F (true,a))^2 ≤ (q*dist (false,b) (true,a))^2 := by
      nlinarith [hbaseHi,h2,hxq]
    constructor
    · exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg (by norm_num : 2 ≠ 0)).1 hlow
    · exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg hq0 dist_nonneg) (by norm_num : 2 ≠ 0)).1 hhigh
  · have he := hFsq true true a b
    simp only [T,Z,↓reduceIte,sub_self,zero_pow,add_zero] at he
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0, mul_pow] at he
    have hd : ‖(u a-c)-(u b-c)‖ = dist (u a) (u b) := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [hd] at he
    have hαδ : 0 ≤ α * dist (u a) (u b) := mul_nonneg hα0 dist_nonneg
    have heq : dist (F (true,a)) (F (true,b)) = α * dist (u a) (u b) := by
      nlinarith [dist_nonneg (x := F (true,a)) (y := F (true,b)),
        dist_nonneg (x := u a) (y := u b)]
    rw [heq, ht a b]
    by_cases hab : a=b
    · subst b; simp
    · have hδ := hsep a b hab
      have hδq := hdiam a b
      have hδ0 : 0 ≤ dist (u a) (u b) := le_trans (by norm_num) hδ
      have hmul1 := mul_nonneg hs.le (mul_nonneg hδ0 (sub_nonneg.mpr hδq))
      have hmul2 := mul_nonneg hs.le (mul_nonneg (mul_nonneg hq0 hδ0) (by linarith : 0 ≤ dist (u a) (u b)-1))
      dsimp [α]
      constructor
      · nlinarith only [hmul1]
      · nlinarith only [hmul2]
