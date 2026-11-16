import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixQPermanent

/-!
# matrix_q_permanent_three_of_diag_one

Topic: combinatorics   Node: 82fe52f98573

Provenance: formalization of a published result. Source: arXiv:2611.14694, Proof of Proposition 5.1 -- Real positive definite counterexamples to a monotonicity conjecture for the q-permanent

For any real symmetric 3-by-3 matrix A with all diagonal entries equal to 1, writing x = A 0 1, y = A 1 2, and z = A 0 2, the q-permanent of A at q equals 1 + (x^2 + y^2) * q + 2 * x * y * z * q^2 + z^2 * q^3.
-/

/-- The q-permanent of a real symmetric 3x3 matrix with unit diagonal equals 1 + (x^2+y^2)q + 2xyz q^2 + z^2 q^3. -/
theorem matrix_q_permanent_three_of_diag_one (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymm : A.IsSymm) (hdiag : ∀ i, A i i = 1) (q : ℝ) :
    let x := A 0 1
    let y := A 1 2
    let z := A 0 2
    matrix_q_permanent q A = 1 + (x ^ 2 + y ^ 2) * q + 2 * x * y * z * q ^ 2 + z ^ 2 * q ^ 3 := by
  intro x y z
  let p0 : Equiv.Perm (Fin 3) := 1
  let p1 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let p2 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let p3 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let p4 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let p5 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1
  unfold matrix_q_permanent
  have h_univ : (Finset.univ : Finset (Equiv.Perm (Fin 3))) = {p0, p1, p2, p3, p4, p5} := by decide
  rw [show (∑ σ : Equiv.Perm (Fin 3), _) = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))), _ from rfl]
  rw [h_univ]
  have ne0 : p0 ∉ ({p1, p2, p3, p4, p5} : Finset (Equiv.Perm (Fin 3))) := by decide
  have ne1 : p1 ∉ ({p2, p3, p4, p5} : Finset (Equiv.Perm (Fin 3))) := by decide
  have ne2 : p2 ∉ ({p3, p4, p5} : Finset (Equiv.Perm (Fin 3))) := by decide
  have ne3 : p3 ∉ ({p4, p5} : Finset (Equiv.Perm (Fin 3))) := by decide
  have ne4 : p4 ∉ ({p5} : Finset (Equiv.Perm (Fin 3))) := by decide
  rw [Finset.sum_insert ne0, Finset.sum_insert ne1, Finset.sum_insert ne2,
      Finset.sum_insert ne3, Finset.sum_insert ne4, Finset.sum_singleton]
  dsimp only
  have h_inv0 : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2 ∧ p0 p.2 < p0 p.1)).card = 0 := by decide
  have h_inv1 : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2 ∧ p1 p.2 < p1 p.1)).card = 1 := by decide
  have h_inv2 : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2 ∧ p2 p.2 < p2 p.1)).card = 1 := by decide
  have h_inv3 : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2 ∧ p3 p.2 < p3 p.1)).card = 3 := by decide
  have h_inv4 : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2 ∧ p4 p.2 < p4 p.1)).card = 2 := by decide
  have h_inv5 : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 < p.2 ∧ p5 p.2 < p5 p.1)).card = 2 := by decide
  rw [h_inv0, h_inv1, h_inv2, h_inv3, h_inv4, h_inv5]
  repeat rw [Fin.prod_univ_three]
  have hp0_0 : p0 0 = 0 := rfl
  have hp0_1 : p0 1 = 1 := rfl
  have hp0_2 : p0 2 = 2 := rfl
  have hp1_0 : p1 0 = 1 := rfl
  have hp1_1 : p1 1 = 0 := rfl
  have hp1_2 : p1 2 = 2 := rfl
  have hp2_0 : p2 0 = 0 := rfl
  have hp2_1 : p2 1 = 2 := rfl
  have hp2_2 : p2 2 = 1 := rfl
  have hp3_0 : p3 0 = 2 := rfl
  have hp3_1 : p3 1 = 1 := rfl
  have hp3_2 : p3 2 = 0 := rfl
  have hp4_0 : p4 0 = 1 := rfl
  have hp4_1 : p4 1 = 2 := rfl
  have hp4_2 : p4 2 = 0 := rfl
  have hp5_0 : p5 0 = 2 := rfl
  have hp5_1 : p5 1 = 0 := rfl
  have hp5_2 : p5 2 = 1 := rfl
  rw [hp0_0, hp0_1, hp0_2, hp1_0, hp1_1, hp1_2, hp2_0, hp2_1, hp2_2,
      hp3_0, hp3_1, hp3_2, hp4_0, hp4_1, hp4_2, hp5_0, hp5_1, hp5_2]
  have hd0 : A 0 0 = 1 := hdiag 0
  have hd1 : A 1 1 = 1 := hdiag 1
  have hd2 : A 2 2 = 1 := hdiag 2
  have hs01 : A 1 0 = A 0 1 := hsymm.apply 0 1
  have hs12 : A 2 1 = A 1 2 := hsymm.apply 1 2
  have hs02 : A 2 0 = A 0 2 := hsymm.apply 0 2
  rw [hd0, hd1, hd2, hs01, hs12, hs02]
  change 1 * (1 * 1 * 1) +
    (q ^ 1 * (x * x * 1) +
      (q ^ 1 * (1 * y * y) +
        (q ^ 3 * (z * 1 * z) +
          (q ^ 2 * (x * y * z) + q ^ 2 * (z * x * y))))) =
    1 + (x ^ 2 + y ^ 2) * q + 2 * x * y * z * q ^ 2 + z ^ 2 * q ^ 3
  ring
