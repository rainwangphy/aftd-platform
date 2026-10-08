import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorDist
import AFTD.Kb.Tcs.Support

/-!
# Cslib.Probability.PMF.posteriorDist_apply

Topic: randomness   Node: 7bed36987d3a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.posteriorDist_apply`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Probability.PMF.posteriorDist_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
@[simp]
theorem Cslib.Probability.PMF.posteriorDist_apply (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) (a : α) :
    posteriorDist p f b hb a =
      (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
        (p.bind f) b :=
  rfl
