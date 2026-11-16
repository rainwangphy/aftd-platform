import AFTD.Prelude
import AFTD.Kb.Tcs.EmbedsIntoHilbertWithDistortion
import AFTD.Kb.Tcs.OseQuadInequality
import AFTD.Kb.Tcs.OseTwoPieceUnboundedNegativeDirections

/-!
# ose_two_piece_block_exact_hilbert_distortion

Topic: algorithms   Node: fdddc42783fb

Provenance: original. Related work: arXiv:2611.08546, Section 1.1; distortion of the rational-block negative-direction obstruction

Let m be a positive natural number. Consider any metric on triples of a side, one of m blocks, and a bit, with distance zero on the diagonal, 5/2 between opposite sides in the same block, and 4 between all other distinct points. For every real D, the entire metric has a Hilbert embedding with distances between the original distances and D times them if and only if D is at least 4 sqrt(2)/5.
-/

open scoped RealInnerProductSpace

private lemma ose_two_piece_block_exact_hilbert_distortion_inner_single_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : ι) (a b : ℝ) :
    ⟪(EuclideanSpace.single p a : EuclideanSpace ℝ ι), EuclideanSpace.single q b⟫ = if p = q then a * b else 0 := by
  rw [EuclideanSpace.inner_single_left]
  rw [EuclideanSpace.single_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

private noncomputable def ose_two_piece_block_exact_hilbert_distortion_embed (m : ℕ)
    (x : Bool × (Fin m × Bool)) : EuclideanSpace ℝ (Fin m ⊕ (Fin m × Bool)) :=
  EuclideanSpace.single (Sum.inl x.2.1) (2:ℝ)
    + EuclideanSpace.single (Sum.inr (x.2.1, x.1)) (if x.2.2 then 2 else -2)

private lemma ose_two_piece_block_exact_hilbert_distortion_embed_inner (m : ℕ) (x y : Bool × (Fin m × Bool)) :
    ⟪ose_two_piece_block_exact_hilbert_distortion_embed m x,
      ose_two_piece_block_exact_hilbert_distortion_embed m y⟫
      = (if x.2.1 = y.2.1 then 4 else 0)
      + (if (x.2.1, x.1) = (y.2.1, y.1) then (if x.2.2 then 2 else -2) * (if y.2.2 then 2 else -2) else 0) := by
  unfold ose_two_piece_block_exact_hilbert_distortion_embed
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [ose_two_piece_block_exact_hilbert_distortion_inner_single_single,
      ose_two_piece_block_exact_hilbert_distortion_inner_single_single,
      ose_two_piece_block_exact_hilbert_distortion_inner_single_single,
      ose_two_piece_block_exact_hilbert_distortion_inner_single_single]
  simp only [Sum.inl.injEq, Sum.inr.injEq]
  by_cases h : x.2.1 = y.2.1 <;> simp [Sum.inl_ne_inr, Sum.inr_ne_inl, h] <;> norm_num

private lemma ose_two_piece_block_exact_hilbert_distortion_embed_norm (m : ℕ) (x : Bool × (Fin m × Bool)) :
    ‖ose_two_piece_block_exact_hilbert_distortion_embed m x‖^2 = 8 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [ose_two_piece_block_exact_hilbert_distortion_embed_inner]
  by_cases hb : x.2.2 <;> simp [hb] <;> norm_num

private lemma ose_two_piece_block_exact_hilbert_distortion_embed_dist_sq (m : ℕ) (x y : Bool × (Fin m × Bool)) :
    dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
      (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2
      = 16 - 2*((if x.2.1 = y.2.1 then 4 else 0)
      + (if (x.2.1, x.1) = (y.2.1, y.1) then (if x.2.2 then 2 else -2) * (if y.2.2 then 2 else -2) else 0)) := by
  rw [dist_eq_norm, norm_sub_sq_real, ose_two_piece_block_exact_hilbert_distortion_embed_norm,
      ose_two_piece_block_exact_hilbert_distortion_embed_norm,
      ose_two_piece_block_exact_hilbert_distortion_embed_inner]
  ring

private lemma ose_two_piece_block_exact_hilbert_distortion_embed_dist (m : ℕ) (x y : Bool × (Fin m × Bool)) :
    dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
      (ose_two_piece_block_exact_hilbert_distortion_embed m y) =
      if x = y then 0 else if x.1 ≠ y.1 ∧ x.2.1 = y.2.1 then Real.sqrt 8 else 4 := by
  have sqrt16 : Real.sqrt 16 = (4:ℝ) := by
    rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    by_cases hb : x.2.1 = y.2.1
    · by_cases hs : x.1 = y.1
      · rw [if_neg (by intro h; exact h.1 hs)]
        have hbit : x.2.2 ≠ y.2.2 := by
          intro h; exact hxy (by ext <;> simp_all)
        have hd : dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
            (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2 = 16 := by
          rw [ose_two_piece_block_exact_hilbert_distortion_embed_dist_sq]
          by_cases hxb : x.2.2 <;> by_cases hyb : y.2.2 <;> simp_all <;> norm_num
        rw [show dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
              (ose_two_piece_block_exact_hilbert_distortion_embed m y)
              = Real.sqrt (dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
              (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2) from
            (Real.sqrt_sq (dist_nonneg)).symm, hd, sqrt16]
      · rw [if_pos ⟨hs, hb⟩]
        have hd : dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
            (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2 = 8 := by
          rw [ose_two_piece_block_exact_hilbert_distortion_embed_dist_sq]
          simp [hb, hs]
          norm_num
        rw [show dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
              (ose_two_piece_block_exact_hilbert_distortion_embed m y)
              = Real.sqrt (dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
              (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2) from
            (Real.sqrt_sq (dist_nonneg)).symm, hd]
    · rw [if_neg (by intro h; exact hb h.2)]
      have hd : dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
          (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2 = 16 := by
        rw [ose_two_piece_block_exact_hilbert_distortion_embed_dist_sq]
        simp [hb]
      rw [show dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
            (ose_two_piece_block_exact_hilbert_distortion_embed m y)
            = Real.sqrt (dist (ose_two_piece_block_exact_hilbert_distortion_embed m x)
            (ose_two_piece_block_exact_hilbert_distortion_embed m y)^2) from
          (Real.sqrt_sq (dist_nonneg)).symm, hd, sqrt16]

private theorem ose_two_piece_block_exact_hilbert_distortion_lower (m : ℕ) (hm : 1 ≤ m)
    (M : MetricSpace (Bool × (Fin m × Bool))) :
    letI := M
    (∀ x y : Bool × (Fin m × Bool), dist x y = if x=y then 0 else if x.1 ≠ y.1 ∧ x.2.1=y.2.1 then (5:ℝ)/2 else 4) →
    ∀ D : ℝ, EmbedsIntoHilbertWithDistortion (Bool × (Fin m × Bool)) D → 4 * Real.sqrt 2 / 5 ≤ D := by
  letI := M
  intro hdist D h
  have hi : (0:ℕ) < m := by omega
  let i : Fin m := ⟨0, hi⟩
  let a : Bool × (Fin m × Bool) := (false, i, false)
  let b : Bool × (Fin m × Bool) := (true, i, false)
  let c : Bool × (Fin m × Bool) := (true, i, true)
  let d : Bool × (Fin m × Bool) := (false, i, true)
  obtain ⟨H, instNAG, instIPS, instCS, f, hf⟩ := h
  letI := instNAG
  letI := instIPS
  have hab : dist a b = 5/2 := by rw [hdist]; simp [a, b]
  have hcd : dist c d = 5/2 := by rw [hdist]; simp [c, d]
  have hac : dist a c = 5/2 := by rw [hdist]; simp [a, c]
  have hbd : dist b d = 5/2 := by rw [hdist]; simp [b, d]
  have had : dist a d = 4 := by rw [hdist]; simp [a, d]
  have hbc : dist b c = 4 := by rw [hdist]; simp [b, c]
  have h_img_ab := (hf a b).1
  have h_img_ad := (hf a d).1
  have h_img_bc := (hf b c).1
  have h_img_cd := (hf c d).1
  have h_img_ac := (hf a c).1
  have h_img_bd := (hf b d).1
  have h_up_ab := (hf a b).2
  have h_up_cd := (hf c d).2
  have h_up_ac := (hf a c).2
  have h_up_bd := (hf b d).2
  have hq := ose_quad_inequality H (f a) (f b) (f c) (f d)
  have hLL : dist (f a) (f d) ^ 2 + dist (f b) (f c) ^ 2 ≤
      dist (f a) (f b) ^ 2 + dist (f c) (f d) ^ 2 + dist (f a) (f c) ^ 2 + dist (f b) (f d) ^ 2 := hq
  have hlad : dist (f a) (f d) ≥ 4 := by rw [← had]; exact h_img_ad
  have hlbc : dist (f b) (f c) ≥ 4 := by rw [← hbc]; exact h_img_bc
  have huab : dist (f a) (f b) ≤ D * (5/2) := by rw [← hab]; exact h_up_ab
  have hucd : dist (f c) (f d) ≤ D * (5/2) := by rw [← hcd]; exact h_up_cd
  have huac : dist (f a) (f c) ≤ D * (5/2) := by rw [← hac]; exact h_up_ac
  have hubd : dist (f b) (f d) ≤ D * (5/2) := by rw [← hbd]; exact h_up_bd
  have hDpos : 0 < D := by
    have h1 : (0:ℝ) ≤ dist (f a) (f b) := dist_nonneg
    nlinarith [hab, h_img_ab, h_up_ab]
  have h32 : (32:ℝ) ≤ dist (f a) (f d) ^ 2 + dist (f b) (f c) ^ 2 := by
    nlinarith [sq_nonneg (dist (f a) (f d) - 4), sq_nonneg (dist (f b) (f c) - 4), hlad, hlbc]
  have h25 : dist (f a) (f d) ^ 2 + dist (f b) (f c) ^ 2 ≤ 25 * D ^ 2 := by
    nlinarith [hLL, huab, hucd, huac, hubd, dist_nonneg (x := f a) (y := f b),
      dist_nonneg (x := f c) (y := f d), dist_nonneg (x := f a) (y := f c),
      dist_nonneg (x := f b) (y := f d), sq_nonneg (D * (5/2)), sq_nonneg D]
  have hDsq : (32:ℝ)/25 ≤ D^2 := by nlinarith [h32, h25]
  have hsq : (4 * Real.sqrt 2 / 5)^2 = (32:ℝ)/25 := by
    have h2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [h2]
  have hDnn : 0 ≤ D := le_of_lt hDpos
  exact le_of_sq_le_sq (by rw [hsq]; exact hDsq) hDnn

private theorem ose_two_piece_block_exact_hilbert_distortion_upper (m : ℕ)
    (M : MetricSpace (Bool × (Fin m × Bool))) :
    letI := M
    (∀ x y : Bool × (Fin m × Bool), dist x y = if x=y then 0 else if x.1 ≠ y.1 ∧ x.2.1=y.2.1 then (5:ℝ)/2 else 4) →
    ∀ D : ℝ, 4 * Real.sqrt 2 / 5 ≤ D → EmbedsIntoHilbertWithDistortion (Bool × (Fin m × Bool)) D := by
  letI := M
  intro hdist D hD
  have h5 : (5:ℝ)/2 ≤ Real.sqrt 8 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsq8 : (4 * Real.sqrt 2 / 5) * (5/2) = Real.sqrt 8 := by
    rw [show (8:ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  have hsqrt8le : Real.sqrt 8 ≤ D * (5/2) := by
    rw [← hsq8]; exact mul_le_mul_of_nonneg_right hD (by norm_num)
  have hone : (1:ℝ) ≤ 4 * Real.sqrt 2 / 5 := by
    have h2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2]
  have hfour : (4:ℝ) ≤ D * 4 := by nlinarith [hD, hone]
  refine ⟨EuclideanSpace ℝ (Fin m ⊕ (Fin m × Bool)), inferInstance, inferInstance, inferInstance,
    ose_two_piece_block_exact_hilbert_distortion_embed m, ?_⟩
  intro x y
  rw [ose_two_piece_block_exact_hilbert_distortion_embed_dist, hdist]
  constructor
  · by_cases hxy : x = y
    · simp [hxy]
    · rw [if_neg hxy, if_neg hxy]
      by_cases hc : x.1 ≠ y.1 ∧ x.2.1 = y.2.1
      · rw [if_pos hc, if_pos hc]; exact h5
      · rw [if_neg hc, if_neg hc]
  · by_cases hxy : x = y
    · simp [hxy]
    · rw [if_neg hxy, if_neg hxy]
      by_cases hc : x.1 ≠ y.1 ∧ x.2.1 = y.2.1
      · rw [if_pos hc, if_pos hc]; exact hsqrt8le
      · rw [if_neg hc, if_neg hc]; exact hfour

theorem ose_two_piece_block_exact_hilbert_distortion (m : ℕ) (hm : 1 ≤ m) (M : MetricSpace (Bool × (Fin m × Bool))) :
  letI := M
  (∀ x y : Bool × (Fin m × Bool), dist x y = if x=y then 0 else if x.1 ≠ y.1 ∧ x.2.1=y.2.1 then (5:ℝ)/2 else 4) →
  ∀ D : ℝ, EmbedsIntoHilbertWithDistortion (Bool × (Fin m × Bool)) D ↔ 4 * Real.sqrt 2 / 5 ≤ D := by
  letI := M
  intro hdist D
  constructor
  · intro h
    exact ose_two_piece_block_exact_hilbert_distortion_lower m hm M hdist D h
  · intro hD
    exact ose_two_piece_block_exact_hilbert_distortion_upper m M hdist D hD
