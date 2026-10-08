import AFTD.Prelude

/-!
# Cslib.Probability.PMF.bind_pair_apply

Topic: randomness   Node: 7da9cd8a5edf

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.bind_pair_apply`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Evaluating the "pairing" bind `(do let a ← p; return (a, ← f a))` at `(a, b)` gives the product `p a * f a b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
/-- Evaluating the "pairing" bind `(do let a ← p; return (a, ← f a))` at `(a, b)` gives the product `p a * f a b`. -/
theorem Cslib.Probability.PMF.bind_pair_apply (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) = p a * f a b := by
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.bind_apply]; congr 1; rw [tsum_eq_single b]
    · simp [PMF.pure_apply]
    · intro b' hb'; simp [PMF.pure_apply, hb'.symm]
  · intro a' ha'; rw [PMF.bind_apply]; simp [PMF.pure_apply, ha'.symm]
