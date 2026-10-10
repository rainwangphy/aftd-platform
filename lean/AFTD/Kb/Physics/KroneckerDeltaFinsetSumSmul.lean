import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.finset_sum_smul

Topic: classical_mechanics   Node: fa32cd79dd01

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.finset_sum_smul`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KroneckerDelta.finset_sum_smul
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
lemma KroneckerDelta.finset_sum_smul (s : Finset α) (i : α) (f : α → M) :
    ∑ j ∈ s, δ[i,j] • f j = if i ∈ s then f i else 0 := by
  simp [kroneckerDelta]
