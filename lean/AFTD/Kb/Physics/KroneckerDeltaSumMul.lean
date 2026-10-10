import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.sum_mul

Topic: classical_mechanics   Node: 18d57c2107ee

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.sum_mul`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KroneckerDelta.sum_mul
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
lemma KroneckerDelta.sum_mul [Fintype α] (i j : α) : ∑ k : α, δ[i,k] * δ[k,j] = δ[i,j] := by
  simp [kroneckerDelta]
