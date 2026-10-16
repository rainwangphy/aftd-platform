import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap
import AFTD.Kb.Tcs.MatrixMapOfChoiMatrix
import AFTD.Kb.Tcs.MatrixMapChoiMatrix
import AFTD.Kb.Tcs.MatrixMapMapChoiInv

/-!
# MatrixMap.choi_map_inv

Topic: quantum   Node: 9fc4b69f770a

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.choi_map_inv`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Proves that `MatrixMap.choi_matrix` and `MatrixMap.of_choi_matrix` inverses.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixMap in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
set_option backward.isDefEq.respectTransparency false in
/-- Proves that `MatrixMap.choi_matrix` and `MatrixMap.of_choi_matrix` inverses. -/
@[simp]
theorem MatrixMap.choi_map_inv (M : MatrixMap A B R) : of_choi_matrix (choi_matrix M) = M := by
  -- By definition of `MatrixMap.of_choi_matrix`, we know that applying it to the Choi matrix of `M`
  -- reconstructs `M`.
  ext X b₁ b₂; simp [MatrixMap.of_choi_matrix, MatrixMap.choi_matrix];
  -- By linearity of $M$, we can distribute $M$ over the sum.
  have h_linear : M X = ∑ x : A, ∑ x_1 : A, X x x_1 • M (Matrix.single x x_1 1) := by
    have h_linear : M X = M (∑ x : A, ∑ x_1 : A, X x x_1 • Matrix.single x x_1 1) := by
      congr with i j ; simp ( config := { decide := Bool.true } ) [ Matrix.sum_apply ];
      simp ( config := { decide := Bool.true } ) [ Matrix.single ];
      rw [ Finset.sum_eq_single i ] <;> aesop;
    simp +decide only [h_linear, map_sum, LinearMap.map_smulₛₗ];
    simp +zetaDelta at *;
  -- By linearity of $M$, we can distribute $M$ over the sum and then apply it to each term.
  simp [h_linear, Matrix.sum_apply]
