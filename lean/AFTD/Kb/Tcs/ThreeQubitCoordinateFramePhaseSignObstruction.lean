import AFTD.Prelude

/-!
# three_qubit_coordinate_frame_phase_sign_obstruction

Topic: quantum   Node: 079d7e807280

Provenance: helper lemma. Exact certificate for AFTD computation 29928, related to arXiv:2611.16921 Section VII.

For the displayed real trilinear tensor, the quartic phase invariant is strictly positive on each of the six indicated positively oriented coordinate frames. Thus those frames alone do not supply opposite signs for an arbitrary tensor; this is not a physical-state counterexample.
-/

theorem three_qubit_coordinate_frame_phase_sign_obstruction :
  let T : Fin 3 → Fin 3 → Fin 3 → ℂ :=
    ![![![0,0,1], ![0,0,0], ![1,2,0]],
      ![![2,0,0], ![0,-1,2], ![0,-1,0]],
      ![![2,-1,0], ![0,1,0], ![0,0,0]]]
  let e0 : Fin 3 → ℂ := ![1,0,0]
  let e1 : Fin 3 → ℂ := ![0,1,0]
  let e2 : Fin 3 → ℂ := ![0,0,1]
  let tri := fun (x y z : Fin 3 → ℂ) => ∑ i, ∑ j, ∑ k, T i j k * x i * y j * z k
  let F := fun (a b c : Fin 3 → ℂ) =>
    let p : Fin 3 → ℂ := fun i => b i + Complex.I*c i
    let q : Fin 3 → ℂ := fun i => c i + Complex.I*a i
    let r : Fin 3 → ℂ := fun i => a i + Complex.I*b i
    let z0 := tri p q r
    let z1 := tri p q (fun i => star (r i))
    let z2 := tri p (fun i => star (q i)) r
    let z3 := tri (fun i => star (p i)) q r
    (z0 * star (z1*z2*z3)).im
  F e0 e1 e2 = 64 ∧ F e0 e2 (-e1) = 64 ∧
  F e1 e0 (-e2) = 16 ∧ F e1 e2 e0 = 4 ∧
  F e2 e0 e1 = 24 ∧ F e2 e1 (-e0) = 16 := by
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Complex.star_def, Complex.mul_re, Complex.mul_im]
