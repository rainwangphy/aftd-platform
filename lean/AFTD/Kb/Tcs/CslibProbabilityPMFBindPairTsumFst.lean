import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFBindPairApply

/-!
# Cslib.Probability.PMF.bind_pair_tsum_fst

Topic: randomness   Node: 99c488466d55

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.bind_pair_tsum_fst`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Summing the pairing bind over the first component gives the marginal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
/-- Summing the pairing bind over the first component gives the marginal. -/
theorem Cslib.Probability.PMF.bind_pair_tsum_fst (p : PMF α) (f : α → PMF β) (b : β) :
    ∑' a, (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) =
      (p.bind f) b := by
  simp_rw [bind_pair_apply, PMF.bind_apply]
