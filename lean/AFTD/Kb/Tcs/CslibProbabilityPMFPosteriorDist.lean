import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFPosteriorHasSum

/-!
# Cslib.Probability.PMF.posteriorDist

Topic: randomness   Node: e166ba707839

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.posteriorDist`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The posterior distribution `Pr[A = a | B = b]` as a `PMF`, given `a ← p`, `b ← f a`, and that `b` has positive marginal probability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
/-- The posterior distribution `Pr[A = a | B = b]` as a `PMF`, given `a ← p`, `b ← f a`, and that `b` has positive marginal probability. -/
noncomputable def Cslib.Probability.PMF.posteriorDist (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) : PMF α :=
  ⟨fun a =>
    (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
      (p.bind f) b,
   posterior_hasSum p f b hb⟩
