import AFTD.Prelude

/-!
# op1370_weight_matrix_uniform

Topic: combinatorics   Node: cd7041285f01

Provenance: helper lemma.

Uniform weights scale a sum of rank-one matrices equal to the identity.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_weight_matrix_uniform
    {ι V K : Type*} [Fintype ι] [Fintype V] [DecidableEq V] [CommRing K]
    (L R : ι → V → K) (t : K)
    (hid : (∑ i, Matrix.vecMulVec (L i) (R i)) = (1 : Matrix V V K)) :
    (∑ i, t • Matrix.vecMulVec (L i) (R i)) = t • (1 : Matrix V V K) := by
  rw [← Finset.smul_sum, hid]
