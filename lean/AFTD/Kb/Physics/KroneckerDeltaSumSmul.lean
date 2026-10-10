import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.sum_smul

Topic: classical_mechanics   Node: b24d9d10fbc9

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.sum_smul`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KroneckerDelta.sum_smul
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
@[simp]
lemma KroneckerDelta.sum_smul [Fintype α] (i : α) (f : α → M) : ∑ j : α, δ[i,j] • f j = f i := by
  simp [kroneckerDelta]
