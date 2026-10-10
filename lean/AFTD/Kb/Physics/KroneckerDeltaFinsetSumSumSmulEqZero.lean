import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaFinsetSumSmul

/-!
# KroneckerDelta.finset_sum_sum_smul_eq_zero

Topic: classical_mechanics   Node: d5f41205ef65

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.finset_sum_sum_smul_eq_zero`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KroneckerDelta.finset_sum_sum_smul_eq_zero
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
lemma KroneckerDelta.finset_sum_sum_smul_eq_zero {s s' : Finset α} {f : α → α → M}
    (hf : ∀ i ∈ s ∩ s', f i i = 0) : ∑ i ∈ s, ∑ j ∈ s', δ[i,j] • f i j = 0 := by
  simp only [finset_sum_smul, Finset.sum_ite_mem]
  rw [← sum_coe_sort]
  simp [hf]
