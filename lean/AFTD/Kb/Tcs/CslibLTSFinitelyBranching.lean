import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSImageFinite
import AFTD.Kb.Tcs.CslibLTSOutgoingLabels

/-!
# Cslib.LTS.FinitelyBranching

Topic: computability   Node: b08671e7a27f

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.FinitelyBranching`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

An LTS is finitely branching if it is image-finite and all states have finite sets of outgoing labels.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An LTS is finitely branching if it is image-finite and all states have finite sets of outgoing labels. -/
class Cslib.LTS.FinitelyBranching where
  [image_finite : lts.ImageFinite]
  [finite_state : ∀ s, Finite (lts.outgoingLabels s)]

attribute [instance] Cslib.LTS.FinitelyBranching.image_finite Cslib.LTS.FinitelyBranching.finite_state
