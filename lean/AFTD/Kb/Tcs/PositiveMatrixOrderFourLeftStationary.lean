import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPerronFrobenius
import AFTD.Kb.Optimization.Wsum

/-!
# positive_matrix_order_four_left_stationary

Topic: graphs   Node: e0454d71c6cb

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

A strictly positive order-four real matrix with constant row sum has a strictly positive normalized left eigenvector with that eigenvalue.
-/

theorem positive_matrix_order_four_left_stationary
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : ∀ i j, 0 < M i j)
    (r : ℝ) (hr : ∀ i, ∑ j, M i j = r) :
    ∃ π : Fin 4 → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i) = 1 ∧
      ∀ j, ∑ i, π i * M i j = r * π j := by
  obtain ⟨x, y, lam, hlam, hx, hy, hxM, hMy⟩ :=
    EconCSLib.LinearAlgebra.perron_frobenius M hM
  have hsum : (∑ i, x.val i) = 1 := x.property.2
  have hxM' : ∀ j, ∑ i, x.val i * M i j = lam * x.val j := hxM
  have hlamr : lam = r := by
    have he := congrArg (fun f : Fin 4 → ℝ => ∑ j, f j) (funext hxM')
    have hleft : (∑ j, ∑ i, x.val i * M i j) = r := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hr]
      rw [← Finset.sum_mul, hsum, one_mul]
    have hright : (∑ j, lam * x.val j) = lam := by
      rw [← Finset.mul_sum, hsum, mul_one]
    change (∑ j, ∑ i, x.val i * M i j) = ∑ j, lam * x.val j at he
    rw [hleft, hright] at he
    exact he.symm
  exact ⟨x.val, hx, hsum, fun j => by simpa only [hlamr] using hxM' j⟩
