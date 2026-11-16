import AFTD.Prelude

/-!
# op1370_weight_matrix_update

Topic: combinatorics   Node: a4010eb4725f

Provenance: helper lemma.

Changing one weight in a weighted sum of rank-one matrices changes the sum by the corresponding rank-one update.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_weight_matrix_update
    {ι V K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (q : ι → K) (L R : ι → V → K) (x : ι) (t : K) :
    (∑ i, (q i + if i = x then t else 0) • Matrix.vecMulVec (L i) (R i)) =
      (∑ i, q i • Matrix.vecMulVec (L i) (R i)) + t • Matrix.vecMulVec (L x) (R x) := by
  classical
  simp only [add_smul, Finset.sum_add_distrib]
  congr 1
  simp
