import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixMap

/-!
# MatrixMap.id

Topic: quantum   Node: cb86a520eaf8

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap.id`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Alias of LinearMap.id, but specifically as a MatrixMap.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A] in
variable [Semiring R] in
variable (A R) in
/-- Alias of LinearMap.id, but specifically as a MatrixMap. -/
@[reducible]
def MatrixMap.id : MatrixMap A A R := LinearMap.id
