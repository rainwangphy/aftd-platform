import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMapChoiMatrix
import AFTD.Kb.Tcs.MatrixMapOfChoiMatrix
import AFTD.Kb.Tcs.MatrixMap

/-!
# MatrixMap.map_choi_inv

Topic: quantum   Node: b35eea8f7dfa

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.map_choi_inv`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Proves that `MatrixMap.of_choi_matrix` and `MatrixMap.choi_matrix` inverses.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixMap in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
set_option backward.isDefEq.respectTransparency false in
/-- Proves that `MatrixMap.of_choi_matrix` and `MatrixMap.choi_matrix` inverses. -/
@[simp]
theorem MatrixMap.map_choi_inv (M : Matrix (B × A) (B × A) R) : choi_matrix (of_choi_matrix M) = M := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  simp [of_choi_matrix, choi_matrix, Matrix.single, ite_and]
