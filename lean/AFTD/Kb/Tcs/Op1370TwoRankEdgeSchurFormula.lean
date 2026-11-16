import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370TwoRankEdgeDet
import AFTD.Kb.Tcs.Op1370TwoRankEdgeAdjugateNumerator

/-!
# op1370_two_rank_edge_schur_formula

Topic: combinatorics   Node: 06532f03b7bb

Provenance: helper lemma.

The scalar inverse-matrix response of the two-element adjacent-rank matrix is minus one divided by the product of its weights minus one.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_edge_schur_formula
    {K : Type*} [Field K] (a b s : K) (hs : s * s = 1) :
    (fun _ : Fin 2 => (1 : K)) ⬝ᵥ
      ((!![a + s, a - b; -s, b - s] : Matrix (Fin 2) (Fin 2) K)⁻¹.mulVec ![s, -s]) =
      (-1 : K) / (a * b - 1) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    op1370_two_rank_edge_det a b s hs, op1370_two_rank_edge_adjugate_numerator a b s hs]
  simp [div_eq_mul_inv, mul_comm]
