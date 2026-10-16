import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap

/-!
# MatrixMap.choi_matrix

Topic: quantum   Node: 237241ecbfc3

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.choi_matrix`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Choi matrix of a given linear matrix map. Note that this is defined even for things that aren't CPTP, it's just rarely talked about in those contexts. This is the inverse of `MatrixMap.of_choi_matrix`. Compare with `MatrixMap.toMatrix`, which gives the transfer matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
/-- Choi matrix of a given linear matrix map. Note that this is defined even for things that aren't CPTP, it's just rarely talked about in those contexts. This is the inverse of `MatrixMap.of_choi_matrix`. Compare with `MatrixMap.toMatrix`, which gives the transfer matrix. -/
def MatrixMap.choi_matrix (M : MatrixMap A B R) : Matrix (B × A) (B × A) R :=
  fun (j₁,i₁) (j₂,i₂) ↦ M (Matrix.single i₁ i₂ 1) j₁ j₂
