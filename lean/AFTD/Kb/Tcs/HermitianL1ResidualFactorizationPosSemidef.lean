import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianL1DiagonalDominancePosSemidef

/-!
# hermitian_l1_residual_factorization_pos_semidef

Topic: quantum   Node: e353ae4540f0

Provenance: helper lemma. Residual factorization method for OP-2299, experiments 40944 and 41047.

A positive multiple of a complex matrix is positive semidefinite if it is a Gram matrix plus a Hermitian diagonally dominant residual.
-/

open scoped Matrix ComplexOrder

theorem hermitian_l1_residual_factorization_pos_semidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (G B R : Matrix n n ℂ) (c : ℝ) (hc : 0 < c)
    (hR : R.IsHermitian)
    (hdom : ∀ i, (∑ j ∈ Finset.univ.erase i, (|(R i j).re| + |(R i j).im|)) ≤ (R i i).re)
    (hfactor : c • G = B * Bᴴ + R) : G.PosSemidef := by
  have hres := hermitian_l1_diagonal_dominance_pos_semidef R hR hdom
  have hscaled : (c • G).PosSemidef := by
    rw [hfactor]
    exact (Matrix.posSemidef_self_mul_conjTranspose B).add hres
  have h := hscaled.smul (le_of_lt (inv_pos.mpr hc))
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] using h
