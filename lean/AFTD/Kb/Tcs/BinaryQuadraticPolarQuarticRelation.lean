import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryAffineQuadraticFourthDifference
import AFTD.Kb.Tcs.BinaryQuadraticFourCubeExpansion

/-!
# binary_quadratic_polar_quartic_relation

Topic: quantum   Node: 14b3b3c16b8a

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

If twice the binary lift of a quadratic form has zero fourth alternating difference on every four-direction cube, its polar bilinear form satisfies every four-index alternating relation.
-/

theorem binary_quadratic_polar_quartic_relation {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hfour : ∀ u : Fin 4 → V,
      (∑ x : Fin 4 → ZMod 2,
        (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
          (2 * ((Q (∑ i : Fin 4, x i • u i)).val : ZMod 8))) = 0) :
    ∀ v w y z : V,
      Q.polarBilin v w * Q.polarBilin y z +
      Q.polarBilin v y * Q.polarBilin w z +
      Q.polarBilin v z * Q.polarBilin w y = 0 := by
  intro v w y z
  let u : Fin 4 → V := ![v,w,y,z]
  have hf := hfour u
  have he := binary_affine_quadratic_fourth_difference
    (Q.polarBilin v w) (Q.polarBilin v y) (Q.polarBilin v z)
    (Q.polarBilin w y) (Q.polarBilin w z) (Q.polarBilin y z)
    0 (fun i : Fin 4 => Q (u i))
  have hcube : ∀ x : Fin 4 → ZMod 2,
      Q (∑ i : Fin 4, x i • u i) =
        Q.polarBilin v w*x 0*x 1 + Q.polarBilin v y*x 0*x 2 +
        Q.polarBilin v z*x 0*x 3 + Q.polarBilin w y*x 1*x 2 +
        Q.polarBilin w z*x 1*x 3 + Q.polarBilin y z*x 2*x 3 +
        0 + ∑ i : Fin 4, Q (u i)*x i := by
    intro x
    rw [binary_quadratic_four_cube_expansion]
    simp [u, Fin.sum_univ_succ]
    ring
  simp_rw [hcube] at hf
  rw [he] at hf
  have hzero : ∀ r : ZMod 2, 4 * (r.val : ZMod 8) = 0 → r = 0 := by decide
  exact hzero _ hf
