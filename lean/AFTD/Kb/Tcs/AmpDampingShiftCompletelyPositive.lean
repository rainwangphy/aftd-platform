import AFTD.Prelude
import AFTD.Kb.Tcs.AmpDampingGenerator
import AFTD.Kb.Tcs.SuperopExp
import AFTD.Kb.Tcs.HasKrausRepresentation
import AFTD.Kb.Tcs.PAmpDamping
import AFTD.Kb.Tcs.VAmpDamping

/-!
# amp_damping_shift_completely_positive

Topic: quantum   Node: c4da8044ce6b

Provenance: formalization of a published result. Source: arXiv:2610.37187 Proposition 9 (eq. 7.1), complete positivity of e^{tL_c}

For every integer $d \ge 2$ and every real number $c$, let $G$ be the amplitude-damping generator $G(X) = V X V^\dagger - \tfrac12(PX + XP)$ on $M_d(\mathbb{C})$, with $V = |0\rangle\langle 1|$ and $P = |1\rangle\langle 1|$, and let $L_c = G + c\,\mathrm{id}$ (a $\mathbb{C}$-linear map on $M_d(\mathbb{C})$, with the real $c$ viewed in $\mathbb{C}$). Then for every real $t \ge 0$ the map $e^{tL_c}$ (the exponential of $t L_c$, computed through its matrix in the basis of matrix units) has a Kraus representation $X \mapsto \sum_i K_i X K_i^\dagger$, i.e. is completely positive.
-/

theorem amp_damping_cp_apply_entry (d : ℕ) (h : 2 ≤ d) (c : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ((amp_damping_generator d h + (c : ℂ) • LinearMap.id :
      Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) X) i j =
      (if i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩ then X ⟨1, by omega⟩ ⟨1, by omega⟩ else 0)
      - (1/2 : ℂ) * ((if i = ⟨1, by omega⟩ then X i j else 0) + (if j = ⟨1, by omega⟩ then X i j else 0))
      + c * X i j := by
  simp only [amp_damping_generator, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp [v_amp_damping, p_amp_damping, Matrix.mul_apply, Matrix.star_apply, ite_and,
    Finset.sum_ite_eq']
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hi : i = ⟨1, by omega⟩ <;> by_cases hj : j = ⟨1, by omega⟩ <;> simp [hi, hj]

theorem amp_damping_cp_superop_exp_eigen (d : ℕ) (L : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ) (μ : ℂ)
    (Y : Matrix (Fin d) (Fin d) ℂ) (hY : L Y = μ • Y) :
    superop_exp d L t Y = NormedSpace.exp ((t : ℂ) * μ) • Y := by
  set b := Matrix.stdBasis ℂ (Fin d) (Fin d)
  set M := LinearMap.toMatrix b b L with hM
  set v := b.repr Y
  have hMv : Matrix.mulVec M v = μ • v := by
    rw [hM, LinearMap.toMatrix_mulVec_repr, hY, map_smul]
    simp [v]
  set C : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := Matrix.of fun l _ => v l with hC
  have hsemi : SemiconjBy C (algebraMap ℂ _ ((t : ℂ) * μ)) ((t : ℂ) • M) := by
    unfold SemiconjBy
    ext l j
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_apply]
    have := congrFun hMv l
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [hC, Matrix.of_apply, smul_eq_mul]
    rw [this]
    ring
  have h2 : C * NormedSpace.exp (algebraMap ℂ _ ((t : ℂ) * μ)) = NormedSpace.exp ((t : ℂ) • M) * C := by
    open scoped Matrix.Norms.Operator in exact (hsemi.exp_right).eq
  have h3 : NormedSpace.exp (algebraMap ℂ (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ((t : ℂ) * μ)) =
      algebraMap ℂ _ (NormedSpace.exp ((t : ℂ) * μ)) := by
    open scoped Matrix.Norms.Operator in exact (NormedSpace.algebraMap_exp_comm _).symm
  rw [h3, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one] at h2
  have hrep : ∀ l, b.repr (superop_exp d L t Y) l = Matrix.mulVec (NormedSpace.exp ((t : ℂ) • M)) v l := by
    intro l
    rw [← LinearMap.toMatrix_mulVec_repr b b]
    rw [show superop_exp d L t = Matrix.toLin b b (NormedSpace.exp ((t : ℂ) • M)) from rfl,
      LinearMap.toMatrix_toLin]
  apply b.repr.injective
  ext l
  rw [hrep l, map_smul, Finsupp.smul_apply]
  have := congrFun (congrFun h2 l) l
  simp only [Matrix.smul_apply, hC, Matrix.of_apply, Matrix.mul_apply, smul_eq_mul] at this
  simp only [Matrix.mulVec, dotProduct]
  rw [← this]
  rfl

theorem amp_damping_cp_eigen_single (d : ℕ) (h : 2 ≤ d) (c : ℝ) (i j : Fin d)
    (hij : ¬ (i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩)) :
    ((amp_damping_generator d h + (c : ℂ) • LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
      (Matrix.single i j 1)) =
      ((c : ℂ) - (1/2 : ℂ) * ((if i = ⟨1, by omega⟩ then 1 else 0) + (if j = ⟨1, by omega⟩ then 1 else 0))) •
        Matrix.single i j 1 := by
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  ext a b
  rw [amp_damping_cp_apply_entry]
  simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  have hc : ∀ x : Fin d, x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨
      (x ≠ ⟨0, by omega⟩ ∧ x ≠ ⟨1, by omega⟩) := fun x => by tauto
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    have h11 : ¬ ((⟨1, by omega⟩ : Fin d) = i ∧ (⟨1, by omega⟩ : Fin d) = j) := fun hh => hij ⟨hh.1.symm, hh.2.symm⟩
    by_cases hi : i = ⟨1, by omega⟩ <;> by_cases hj : j = ⟨1, by omega⟩ <;> simp_all <;>
      first | ring | tauto
  · simp only [hab, if_false, mul_zero]
    have h11 : ¬ (a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩) ∨
        ¬ (i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩) := Or.inr hij
    by_cases ha : a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
    · simp only [ha, and_self, if_true]
      have : ¬ ((i = ⟨1, by omega⟩) ∧ (j = ⟨1, by omega⟩)) := hij
      have hne : ¬ (i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩) := hij
      by_cases hi : i = ⟨1, by omega⟩
      · subst hi
        have hj : j ≠ ⟨1, by omega⟩ := fun e => hij ⟨rfl, e⟩
        simpa using hj
      · simp
        exact fun e => absurd e hi
    · simp [ha]

theorem amp_damping_cp_eigen_w (d : ℕ) (h : 2 ≤ d) (c : ℝ) :
    ((amp_damping_generator d h + (c : ℂ) • LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
      (Matrix.single ⟨1, by omega⟩ ⟨1, by omega⟩ 1 - Matrix.single ⟨0, by omega⟩ ⟨0, by omega⟩ 1)) =
      ((c : ℂ) - 1) • (Matrix.single ⟨1, by omega⟩ ⟨1, by omega⟩ 1 - Matrix.single ⟨0, by omega⟩ ⟨0, by omega⟩ 1) := by
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  ext i j
  rw [amp_damping_cp_apply_entry]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  have hc : ∀ x : Fin d, x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨
      (x ≠ ⟨0, by omega⟩ ∧ x ≠ ⟨1, by omega⟩) := fun x => by tauto
  rcases hc i with rfl | rfl | ⟨hi0, hi1⟩ <;> rcases hc j with rfl | rfl | ⟨hj0, hj1⟩ <;>
    (try have hi0' := Ne.symm hi0) <;> (try have hi1' := Ne.symm hi1) <;>
    (try have hj0' := Ne.symm hj0) <;> (try have hj1' := Ne.symm hj1) <;>
    simp [h01, h01.symm, *] <;> ring

theorem amp_damping_shift_completely_positive (d : ℕ) (h : 2 ≤ d) (c t : ℝ) (ht : 0 ≤ t) :
    has_kraus_representation d (superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t) := by
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set a0 : ℂ := ((Real.exp (c * t / 2) : ℝ) : ℂ) with ha0
  set a1 : ℂ := ((Real.exp (c * t / 2 - t / 2) : ℝ) : ℂ) with ha1
  set s : ℂ := ((Real.exp (c * t / 2) * Real.sqrt (1 - Real.exp (-t)) : ℝ) : ℂ) with hs
  set K0 : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => if i = ⟨1, by omega⟩ then a1 else a0) with hK0
  set K1 : Matrix (Fin d) (Fin d) ℂ := s • v_amp_damping d h with hK1
  have key : superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t =
      (LinearMap.mulLeft ℂ K0).comp (LinearMap.mulRight ℂ (star K0)) +
      (LinearMap.mulLeft ℂ K1).comp (LinearMap.mulRight ℂ (star K1)) := by
    apply (Matrix.stdBasis ℂ (Fin d) (Fin d)).ext
    rintro ⟨i, j⟩
    rw [Matrix.stdBasis_eq_single]
    have hstarK0 : star K0 = K0 := by
      rw [hK0, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      congr 1; funext x
      simp only [Pi.star_apply, apply_ite star, ha0, ha1, Complex.star_def, Complex.conj_ofReal]
    have hVEV : ∀ i j : Fin d, v_amp_damping d h * Matrix.single i j 1 * star (v_amp_damping d h) =
        if i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩ then Matrix.single ⟨0, by omega⟩ ⟨0, by omega⟩ 1 else 0 := by
      intro i j
      ext a b
      simp only [v_amp_damping, Matrix.mul_apply, Matrix.single_apply, Matrix.star_apply]
      simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, apply_ite (fun m : Matrix (Fin d) (Fin d) ℂ => m a b)]
      simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Matrix.single_apply]
      simp only [apply_ite (starRingEnd ℂ), map_one, map_zero]
      have hc : ∀ x : Fin d, x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨
          (x ≠ ⟨0, by omega⟩ ∧ x ≠ ⟨1, by omega⟩) := fun x => by tauto
      rcases hc a with rfl | rfl | ⟨ha0, ha1⟩ <;> rcases hc b with rfl | rfl | ⟨hb0, hb1⟩ <;>
        (try have ha0' := Ne.symm ha0) <;> (try have hb0' := Ne.symm hb0) <;>
        simp [h01, h01.symm, *]
    by_cases hij : i = ⟨1, by omega⟩ ∧ j = ⟨1, by omega⟩
    · obtain ⟨rfl, rfl⟩ := hij
      have hw : Matrix.single (⟨1, by omega⟩ : Fin d) ⟨1, by omega⟩ (1 : ℂ) =
          (Matrix.single (⟨1, by omega⟩ : Fin d) (⟨1, by omega⟩ : Fin d) 1 -
            Matrix.single (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d) 1) +
            Matrix.single (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d) 1 := by abel
      have h00 : ¬ ((⟨0, by omega⟩ : Fin d) = ⟨1, by omega⟩ ∧ (⟨0, by omega⟩ : Fin d) = ⟨1, by omega⟩) :=
        fun hh => h01 hh.1
      conv_lhs => rw [hw, map_add, amp_damping_cp_superop_exp_eigen d _ t _ _ (amp_damping_cp_eigen_w d h c),
        amp_damping_cp_superop_exp_eigen d _ t _ _ (amp_damping_cp_eigen_single d h c _ _ h00)]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, hstarK0, hK1, star_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (v_amp_damping d h), ← Matrix.mul_assoc, hVEV]
      rw [if_pos (And.intro rfl rfl)]
      have hss : star s * s = ((Real.exp (c * t) - Real.exp (c * t - t) : ℝ) : ℂ) := by
        rw [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
        congr 1
        have hle : 0 ≤ 1 - Real.exp (-t) := by
          have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          linarith
        have := Real.mul_self_sqrt hle
        calc Real.exp (c * t / 2) * √(1 - Real.exp (-t)) * (Real.exp (c * t / 2) * √(1 - Real.exp (-t)))
            = (Real.exp (c * t / 2) * Real.exp (c * t / 2)) * (√(1 - Real.exp (-t)) * √(1 - Real.exp (-t))) := by ring
          _ = Real.exp (c * t) * (1 - Real.exp (-t)) := by rw [← Real.exp_add, this]; congr 2; ring
          _ = Real.exp (c * t) - Real.exp (c * t - t) := by
              rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
      ext a b
      simp only [hK0, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply,
        Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      rw [← Complex.exp_eq_exp_ℂ, ← mul_assoc (star s), hss]
      clear_value s a0 a1
      subst ha0 ha1
      have hc : ∀ x : Fin d, x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨
          (x ≠ ⟨0, by omega⟩ ∧ x ≠ ⟨1, by omega⟩) := fun x => by tauto
      rcases hc a with rfl | rfl | ⟨ha0', ha1'⟩ <;> rcases hc b with rfl | rfl | ⟨hb0, hb1⟩ <;>
        (try have := Ne.symm ha0') <;> (try have := Ne.symm ha1') <;>
        (try have := Ne.symm hb0) <;> (try have := Ne.symm hb1) <;>
        simp [h01, h01.symm, *]
      · rw [show (t : ℂ) * (c - 1) = c * t - t by ring, show (t : ℂ) * c = c * t by ring]; ring
      · rw [← Complex.exp_add]; congr 1; ring
    · rw [amp_damping_cp_superop_exp_eigen d _ t _ _ (amp_damping_cp_eigen_single d h c i j hij)]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, hstarK0, hK1, star_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (v_amp_damping d h), ← Matrix.mul_assoc, hVEV, if_neg hij]
      ext a b
      simp only [hK0, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply,
        Matrix.add_apply, Matrix.zero_apply, smul_zero, add_zero, smul_eq_mul]
      by_cases hab : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hab
        simp only [and_self, if_true, mul_one]
        rw [← Complex.exp_eq_exp_ℂ, ha0, ha1, Complex.ofReal_exp, Complex.ofReal_exp]
        by_cases hi : i = ⟨1, by omega⟩ <;> by_cases hj : j = ⟨1, by omega⟩
        · exact absurd ⟨hi, hj⟩ hij
        all_goals simp only [hi, hj, if_true, if_false]
        all_goals rw [← Complex.exp_add]; congr 1; push_cast; ring
      · simp [hab]
  refine ⟨2, ![K0, K1], fun X => ?_⟩
  rw [key]
  simp [Fin.sum_univ_two, Matrix.mul_assoc]
