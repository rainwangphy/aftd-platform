import AFTD.Prelude
import AFTD.Kb.Tcs.AmpDampingGenerator
import AFTD.Kb.Tcs.SuperopExp
import AFTD.Kb.Tcs.IsTracePreservingLinearMap
import AFTD.Kb.Tcs.PAmpDamping
import AFTD.Kb.Tcs.VAmpDamping

/-!
# amp_damping_shift_trace_preserving_only_if

Topic: quantum   Node: bd2f5358a298

Provenance: formalization of a published result. Source: arXiv:2610.37187 Proposition 9 (eq. 7.1), trace preservation only for c = 0

If $e^{tL_c}$ is trace-preserving for some $t > 0$, then $c = 0$.
-/

theorem amp_damping_tp_std_basis_repr_apply (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d)).repr A (i, j) = A i j := by
  simp [Matrix.stdBasis, Module.Basis.map_repr]

theorem amp_damping_tp_v_star_mul_v (d : ℕ) (h : 2 ≤ d) :
    star (v_amp_damping d h) * v_amp_damping d h = p_amp_damping d h := by
  ext i j
  simp only [v_amp_damping, p_amp_damping, Matrix.mul_apply, Matrix.star_apply]
  simp only [Complex.star_def, map_one, map_zero, apply_ite (starRingEnd ℂ)]
  simp [ite_and, Finset.sum_ite_eq']
  split_ifs <;> rfl

theorem amp_damping_tp_generator_trace (d : ℕ) (h : 2 ≤ d) (Y : Matrix (Fin d) (Fin d) ℂ) :
    (amp_damping_generator d h Y).trace = 0 := by
  simp only [amp_damping_generator, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, amp_damping_tp_v_star_mul_v,
    Matrix.trace_mul_comm Y]
  simp; ring

theorem amp_damping_tp_trace_eq_sum_repr (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    X.trace = ∑ k, (fun k : Fin d × Fin d => if k.1 = k.2 then (1 : ℂ) else 0) k *
      (Matrix.stdBasis ℂ (Fin d) (Fin d)).repr X k := by
  rw [Fintype.sum_prod_type]
  simp [amp_damping_tp_std_basis_repr_apply, Matrix.trace]

theorem amp_damping_tp_trace_std_basis (d : ℕ) (k : Fin d × Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d) k).trace = if k.1 = k.2 then 1 else 0 := by
  rw [Matrix.stdBasis_eq_single]
  simp [Matrix.trace, Matrix.single, ite_and, eq_comm]

theorem amp_damping_tp_trace_row_semiconj (d : ℕ) (h : 2 ≤ d) (c t : ℝ) :
    SemiconjBy (Matrix.of fun (_ : Fin d × Fin d) (k : Fin d × Fin d) => if k.1 = k.2 then (1 : ℂ) else 0)
      ((t : ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d))
        (amp_damping_generator d h + (c : ℂ) • LinearMap.id))
      (algebraMap ℂ (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ((t : ℂ) * c)) := by
  unfold SemiconjBy
  ext i k
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply]
  simp only [LinearMap.toMatrix_apply, Matrix.of_apply]
  have key := amp_damping_tp_trace_eq_sum_repr d (((amp_damping_generator d h + (c : ℂ) • LinearMap.id :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))) (Matrix.stdBasis ℂ (Fin d) (Fin d) k))
  rw [← key]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_add,
    Matrix.trace_smul, amp_damping_tp_generator_trace, amp_damping_tp_trace_std_basis]
  simp [smul_eq_mul]

theorem amp_damping_tp_trace_superop_exp (d : ℕ) (h : 2 ≤ d) (c t : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    (superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t X).trace =
      NormedSpace.exp ((t : ℂ) * c) * X.trace := by
  set b := Matrix.stdBasis ℂ (Fin d) (Fin d)
  set R : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of fun (_ : Fin d × Fin d) (k : Fin d × Fin d) => if k.1 = k.2 then (1 : ℂ) else 0 with hR
  set E := NormedSpace.exp ((t : ℂ) • LinearMap.toMatrix b b
      (amp_damping_generator d h + (c : ℂ) • LinearMap.id)) with hE
  have hsemi : R * E = NormedSpace.exp ((t : ℂ) * c) • R := by
    have h1 := (amp_damping_tp_trace_row_semiconj d h c t)
    have h2 : SemiconjBy R E (NormedSpace.exp (algebraMap ℂ (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        ((t : ℂ) * c))) := by
      open scoped Matrix.Norms.Operator in exact h1.exp_right
    rw [h2.eq]
    have h3 : NormedSpace.exp (algebraMap ℂ (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ((t : ℂ) * c)) =
        algebraMap ℂ (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (NormedSpace.exp ((t : ℂ) * c)) := by
      open scoped Matrix.Norms.Operator in exact (NormedSpace.algebraMap_exp_comm _).symm
    rw [h3, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
  have hrep : b.repr (superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t X) =
      Matrix.mulVec E (b.repr X) := by
    rw [← LinearMap.toMatrix_mulVec_repr b b]
    simp [superop_exp, hE, b, LinearMap.toMatrix_toLin]
  rw [amp_damping_tp_trace_eq_sum_repr, amp_damping_tp_trace_eq_sum_repr, hrep]
  have i0 : Fin d × Fin d := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hrow : ∀ l, ∑ k, (if k.1 = k.2 then (1 : ℂ) else 0) * E k l =
      NormedSpace.exp ((t : ℂ) * c) * (if l.1 = l.2 then (1 : ℂ) else 0) := by
    intro l
    have := congrFun (congrFun hsemi i0) l
    simpa [Matrix.mul_apply, hR] using this
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, ← hrow l, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem amp_damping_shift_trace_preserving_only_if (d : ℕ) (h : 2 ≤ d) (c t : ℝ) (ht : 0 < t)
    (htp : is_trace_preserving_linear_map d (superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t)) : c = 0 := by
  have h00 := htp (Matrix.stdBasis ℂ (Fin d) (Fin d) (⟨0, by omega⟩, ⟨0, by omega⟩))
  rw [amp_damping_tp_trace_superop_exp, amp_damping_tp_trace_std_basis] at h00
  simp only [if_true, mul_one] at h00
  have hreal : Real.exp (t * c) = 1 := by
    have : ((t : ℂ) * c) = ((t * c : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp] at h00
    exact_mod_cast h00
  have htc : t * c = 0 := by simpa using hreal
  rcases mul_eq_zero.mp htc with h1 | h1
  · linarith
  · exact h1
