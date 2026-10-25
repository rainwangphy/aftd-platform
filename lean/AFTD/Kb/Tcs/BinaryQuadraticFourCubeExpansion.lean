import AFTD.Prelude

/-!
# binary_quadratic_four_cube_expansion

Topic: quantum   Node: 1ae1726e6099

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

A binary quadratic form evaluated on a four-direction cube equals the sum of its linear vertex values and the six pairwise polar terms.
-/

theorem binary_quadratic_four_cube_expansion {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (u : Fin 4 → V) (x : Fin 4 → ZMod 2) :
    Q (∑ i : Fin 4, x i • u i) =
      (∑ i : Fin 4, x i * Q (u i)) +
      Q.polarBilin (u 0) (u 1)*x 0*x 1 +
      Q.polarBilin (u 0) (u 2)*x 0*x 2 +
      Q.polarBilin (u 0) (u 3)*x 0*x 3 +
      Q.polarBilin (u 1) (u 2)*x 1*x 2 +
      Q.polarBilin (u 1) (u 3)*x 1*x 3 +
      Q.polarBilin (u 2) (u 3)*x 2*x 3 := by
  have hid : ∀ z : ZMod 2, z*z=z := by decide
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    QuadraticMap.map_add Q, ← QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.map_smul Q, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hid]
  ring!
