import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaSumSmul

/-!
# KroneckerDelta.sum_sum_smul_eq_zero

Topic: classical_mechanics   Node: 18cd867b4f7a

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.sum_sum_smul_eq_zero`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KroneckerDelta.sum_sum_smul_eq_zero
-/

set_option quotPrecheck false
open KroneckerDelta
@[inherit_doc]
local notation "δ[" i "," j "]" => kroneckerDelta i j

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {α M : Type*} [DecidableEq α] in
open Finset in
variable [AddCommMonoid M] in
lemma KroneckerDelta.sum_sum_smul_eq_zero [Fintype α] {f : α → α → M} (hf : ∀ i : α, f i i = 0) :
    ∑ i : α, ∑ j : α, δ[i,j] • f i j = 0 := by
  simp [sum_smul, hf, sum_const_zero]
