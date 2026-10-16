import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMat
import AFTD.Kb.Tcs.HermitianMatInstAddGroup
import AFTD.Kb.Tcs.HermitianMatExt
import AFTD.Kb.Tcs.HermitianMatMat
import AFTD.Kb.Tcs.HermitianMatValEqCoe
import AFTD.Kb.Tcs.HermitianMatMatMk
import AFTD.Kb.Tcs.HermitianMatMkMat
import AFTD.Kb.Tcs.HermitianMatMatApply
import AFTD.Kb.Tcs.HermitianMatConjTransposeMat
import AFTD.Kb.Tcs.HermitianMatInstCoeMatrix
import AFTD.Kb.Tcs.HermitianMatInstFun

/-!
# HermitianMat.instUniqueOfIsEmpty

Topic: quantum   Node: e91bcd9d82bd

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat.instUniqueOfIsEmpty`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HermitianMat.instUniqueOfIsEmpty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMat in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable [AddGroup α] [StarAddMonoid α] in
instance HermitianMat.instUniqueOfIsEmpty [IsEmpty n] : Unique (HermitianMat n α) where
  default := 0
  uniq a := by ext; exact (IsEmpty.false ‹_›).elim
