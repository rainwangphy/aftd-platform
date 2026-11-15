import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixQPermanent

/-!
# matrix_q_permanent_two_of_is_symm

Topic: combinatorics   Node: 9c4aa8d6e16b

Provenance: formalization of a published result. Source: arXiv:2611.14694, Proof of Proposition 5.1 -- Real positive definite counterexamples to a monotonicity conjecture for the q-permanent

For any symmetric 2-by-2 matrix A over a commutative ring R and any parameter q in R, the q-permanent of A equals A 0 0 * A 1 1 + q * (A 0 1)^2.
-/

/-- The q-permanent of a symmetric 2x2 matrix equals A 0 0 * A 1 1 + q * (A 0 1)^2. -/
theorem matrix_q_permanent_two_of_is_symm {R : Type*} [CommRing R]
    (q : R) (A : Matrix (Fin 2) (Fin 2) R) (hsymm : A.IsSymm) :
    matrix_q_permanent q A = A 0 0 * A 1 1 + q * (A 0 1) ^ 2 := by
  unfold matrix_q_permanent
  have h_univ : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have h_ne : (1 : Equiv.Perm (Fin 2)) ∉ ({Equiv.swap 0 1} : Finset (Equiv.Perm (Fin 2))) := by decide
  change (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 2))), _) = _
  rw [h_univ, Finset.sum_insert h_ne, Finset.sum_singleton]
  dsimp only
  have h_inv1 : ((Finset.univ : Finset (Fin 2 × Fin 2)).filter (fun p => p.1 < p.2 ∧ (1 : Equiv.Perm (Fin 2)) p.2 < (1 : Equiv.Perm (Fin 2)) p.1)).card = 0 := by decide
  have h_inv2 : ((Finset.univ : Finset (Fin 2 × Fin 2)).filter (fun p => p.1 < p.2 ∧ (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) p.2 < (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) p.1)).card = 1 := by decide
  rw [h_inv1, h_inv2]
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  have hsymm01 : A 1 0 = A 0 1 := hsymm.apply 0 1
  have h_one0 : (1 : Equiv.Perm (Fin 2)) 0 = 0 := rfl
  have h_one1 : (1 : Equiv.Perm (Fin 2)) 1 = 1 := rfl
  have h_sw0 : (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) 0 = 1 := Equiv.swap_apply_left 0 1
  have h_sw1 : (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) 1 = 0 := Equiv.swap_apply_right 0 1
  rw [h_one0, h_one1, h_sw0, h_sw1, hsymm01]
  ring
