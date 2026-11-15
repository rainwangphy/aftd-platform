import AFTD.Prelude
import AFTD.Kb.Tcs.OseBlockMetricQuadraticCertificate
import AFTD.Kb.Tcs.IsOneStronglyEuclidean

/-!
# ose_two_piece_unbounded_negative_directions

Topic: algorithms   Node: 1bf3db64abaf

Provenance: original. Related work: arXiv:2611.08546, Section 1.1; negative-direction obstruction to a finite-rank reduction

For every natural number m, including zero, let X consist of triples (side, block, bit) with two sides and two bits and m blocks. Give X distance 0 on the diagonal, distance 5/2 between opposite sides in the same block, and distance 4 on every other distinct pair. This is a metric for which each side is 1-strongly Euclidean. For each block i let w_i be 1 on the two points on the false side of block i, -1 on the two points on the true side of block i, and 0 elsewhere. Each w_i has sum zero, and the squared-distance quadratic form on a linear combination sum_i c_i w_i is exactly 14 times sum_i c_i².
-/

private lemma block_indicator_sum {m : ℕ} (i j : Fin m) (A B : ℝ) :
    (∑ x : Fin m, ((if x=i then A else 0) - (if x=j then B else 0))^2) =
      if i=j then (A-B)^2 else A^2+B^2 := by
  classical
  by_cases h : i=j
  · subst j
    simp only [if_pos rfl]
    have heq : ∀ x : Fin m, ((if x=i then A else 0) - (if x=i then B else 0))^2 =
        if x=i then (A-B)^2 else 0 := by
      intro x
      split_ifs <;> ring
    simp_rw [heq]
    simp
  · simp only [if_neg h]
    have heq : ∀ x : Fin m, ((if x=i then A else 0) - (if x=j then B else 0))^2 =
        (if x=i then A^2 else 0) + (if x=j then B^2 else 0) := by
      intro x
      by_cases hi : x=i <;> by_cases hj : x=j <;> simp_all <;> ring
    simp_rw [heq]
    simp [Finset.sum_add_distrib]

private abbrev oseBlockCoord (m : ℕ) := Option (Fin m × Bool × Bool)
private noncomputable def oseBlockCoreVec {m : ℕ} (a : Fin m × Bool) : EuclideanSpace ℝ (oseBlockCoord m) :=
  WithLp.toLp 2 (fun z => match z with
    | none => 0
    | some (i,b,t) => if (i,b)=a then 2 else 0)
private noncomputable def oseBlockOutsideVec {m : ℕ} (j : Fin m) : EuclideanSpace ℝ (oseBlockCoord m) :=
  WithLp.toLp 2 (fun z => match z with
    | none => Real.sqrt 527/16
    | some (i,b,t) => if i=j then 39/32 else 0)

private lemma oseBlockCoreDistSq {m : ℕ} (a b : Fin m × Bool) :
    dist (oseBlockCoreVec a) (oseBlockCoreVec b)^2 = if a=b then 0 else 16 := by
  classical
  rcases a with ⟨i,bi⟩
  rcases b with ⟨j,bj⟩
  cases bi <;> cases bj <;>
    rw [EuclideanSpace.dist_sq_eq] <;>
    simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool] <;>
    simp only [oseBlockCoreVec, oseBlockOutsideVec, WithLp.ofLp_toLp, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, false_and, true_and,
      Real.dist_eq, sq_abs] <;>
    simp only [ite_false, zero_sub, sub_zero, zero_pow, zero_add, add_zero, Finset.sum_add_distrib] <;>
    simp only [neg_sq, ite_pow, OfNat.ofNat_ne_zero, zero_pow, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add, add_zero,
      block_indicator_sum] <;>
    (try split_ifs) <;> norm_num [Finset.sum_ite_eq'] <;> nlinarith

private lemma oseBlockCrossDistSq {m : ℕ} (a : Fin m × Bool) (j : Fin m) :
    dist (oseBlockCoreVec a) (oseBlockOutsideVec j)^2 = if a.1=j then (25 : ℝ)/4 else 16 := by
  classical
  rcases a with ⟨i,b⟩
  have hsqrt : (Real.sqrt 527)^2 = (527 : ℝ) := Real.sq_sqrt (by norm_num)
  cases b <;>
    rw [EuclideanSpace.dist_sq_eq] <;>
    simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool] <;>
    simp only [oseBlockCoreVec, oseBlockOutsideVec, WithLp.ofLp_toLp, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, false_and, true_and,
      Real.dist_eq, sq_abs] <;>
    simp only [ite_false, zero_sub, sub_zero, zero_pow, zero_add, add_zero, Finset.sum_add_distrib] <;>
    simp only [neg_sq, ite_pow, OfNat.ofNat_ne_zero, zero_pow, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add, add_zero,
      block_indicator_sum] <;>
    (try split_ifs) <;> norm_num [Finset.sum_ite_eq'] <;> nlinarith [hsqrt]


private lemma oseBlockSideStrong {m : ℕ} (M : MetricSpace (Bool × (Fin m × Bool)))
    (hdist : letI := M; ∀ x y : Bool × (Fin m × Bool),
      dist x y = if x=y then 0 else if x.1 ≠ y.1 ∧ x.2.1=y.2.1 then (5:ℝ)/2 else 4)
    (s : Bool) : letI := M; IsOneStronglyEuclidean {x : Bool × (Fin m × Bool) | x.1=s} := by
  letI := M
  classical
  intro x
  let U : Set (Bool × (Fin m × Bool)) := {y | y.1=s}
  let f : (U ∪ {x} : Set (Bool × (Fin m × Bool))) → EuclideanSpace ℝ (oseBlockCoord m) :=
    fun y => if y.val.1=s then oseBlockCoreVec y.val.2 else oseBlockOutsideVec x.2.1
  refine ⟨_, inferInstance, inferInstance, inferInstance, f, ?_⟩
  apply Isometry.of_dist_eq
  intro y z
  have hy : y.val.1=s ∨ y.val=x := y.property
  have hz : z.val.1=s ∨ z.val=x := z.property
  have hsame : ∀ (a b : Bool × (Fin m × Bool)), a.1=s → b.1=s →
      dist a b ^ 2 = if a.2=b.2 then 0 else 16 := by
    intro a b ha hb
    have heq : (a=b) ↔ (a.2=b.2) := by
      constructor
      · intro h; cases h; rfl
      · intro h; exact Prod.ext (ha.trans hb.symm) h
    rw [hdist]
    simp only [heq,ha,hb,ne_eq,not_true_eq_false,false_and,if_false]
    split_ifs <;> norm_num
  have hcross : ∀ (a : Bool × (Fin m × Bool)), a.1=s → x.1 ≠ s →
      dist a x ^ 2 = if a.2.1=x.2.1 then (25:ℝ)/4 else 16 := by
    intro a ha hx
    have hne : a ≠ x := by intro h; apply hx; simpa [← h] using ha
    have hside : a.1 ≠ x.1 := by rw [ha]; exact Ne.symm hx
    rw [hdist]
    simp only [hne,if_false]
    simp only [and_iff_right hside]
    split_ifs <;> norm_num
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  change dist (f y) (f z)^2 = dist y.val z.val ^ 2
  by_cases hys : y.val.1=s
  · by_cases hzs : z.val.1=s
    · simp only [f,hys,hzs,if_true,oseBlockCoreDistSq]
      exact (hsame y.val z.val hys hzs).symm
    · have hzx : z.val=x := hz.resolve_left hzs
      have hxs : x.1 ≠ s := by simpa [hzx] using hzs
      simp only [f,hys,hzs,if_true,if_false,oseBlockCrossDistSq]
      simpa [hzx] using (hcross y.val hys hxs).symm
  · have hyx : y.val=x := hy.resolve_left hys
    have hxs : x.1 ≠ s := by simpa [hyx] using hys
    by_cases hzs : z.val.1=s
    · simp only [f,hys,hzs,if_true,if_false,dist_comm (oseBlockOutsideVec _),oseBlockCrossDistSq]
      simpa [hyx,dist_comm] using (hcross z.val hzs hxs).symm
    · have hzx : z.val=x := hz.resolve_left hzs
      simp only [f,hys,hzs,if_false,dist_self,zero_pow]
      have heq : y=z := Subtype.ext (hyx.trans hzx.symm)
      subst z
      simp

theorem ose_two_piece_unbounded_negative_directions (m : ℕ) : let X := Bool × (Fin m × Bool); let w : Fin m → X → ℝ := fun i x => if x.2.1 = i then (if x.1 then -1 else 1) else 0; ∃ M : MetricSpace X, letI := M; (∀ x y : X, dist x y = if x = y then 0 else if x.1 ≠ y.1 ∧ x.2.1 = y.2.1 then (5 : ℝ) / 2 else 4) ∧ IsOneStronglyEuclidean {x : X | x.1 = false} ∧ IsOneStronglyEuclidean {x : X | x.1 = true} ∧ (∀ i : Fin m, ∑ x : X, w i x = 0) ∧ ∀ c : Fin m → ℝ, (∑ x : X, ∑ y : X, (∑ i : Fin m, c i * w i x) * (∑ i : Fin m, c i * w i y) * dist x y ^ 2) = 14 * ∑ i : Fin m, (c i)^2 := by
  obtain ⟨M, hd, hz, hq⟩ := ose_block_metric_quadratic_certificate m
  refine ⟨M, hd, ?_, ?_, hz, hq⟩
  · exact oseBlockSideStrong M hd false
  · exact oseBlockSideStrong M hd true
