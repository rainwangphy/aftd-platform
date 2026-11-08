import AFTD.Prelude
import AFTD.Kb.Tcs.AmpDampingGenerator
import AFTD.Kb.Tcs.VAmpDamping
import AFTD.Kb.Tcs.PAmpDamping

/-!
# amp_damping_shift_trace

Topic: quantum   Node: ef2d561ec2d8

Provenance: formalization of a published result. Source: arXiv:2610.37187 Proposition 9 (eq. 7.1), the trace identity

For every integer $d \ge 2$ and every real number $c$, let $G$ be the amplitude-damping generator $G(X) = V X V^\dagger - \tfrac12(PX + XP)$ on $M_d(\mathbb{C})$, with $V = |0\rangle\langle 1|$ and $P = |1\rangle\langle 1|$, and let $L_c = G + c\,\mathrm{id}$ (a $\mathbb{C}$-linear map on $M_d(\mathbb{C})$, with the real $c$ viewed in $\mathbb{C}$). Then the trace of $L_c$ as a linear map on $M_d(\mathbb{C})$ equals $c d^2 - d$ (as a complex number).
-/

theorem amp_damping_std_basis_repr_apply (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (Matrix.stdBasis ℂ (Fin d) (Fin d)).repr A (i, j) = A i j := by
  simp [Matrix.stdBasis, Module.Basis.map_repr]

theorem amp_damping_shift_trace (d : ℕ) (h : 2 ≤ d) (c : ℝ) :
    LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (amp_damping_generator d h + (c : ℂ) • LinearMap.id) = (c : ℂ) * (d : ℂ) ^ 2 - d := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rw [Fintype.sum_prod_type]
  simp [amp_damping_generator, Matrix.stdBasis_eq_single, v_amp_damping, p_amp_damping,
    Matrix.mul_apply, Matrix.single, Finset.sum_add_distrib, amp_damping_std_basis_repr_apply,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  ring
