import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSFinitelyBranching
import AFTD.Kb.Tcs.CslibLTSFiniteStateImageFinite
import AFTD.Kb.Tcs.CslibLTSOutgoingLabels

/-!
# Cslib.LTS.FinitelyBranching.of_finite

Topic: computability   Node: 814a4c75f2fc

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.FinitelyBranching.of_finite`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every LTS with finite types for states and labels is also finitely branching.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Every LTS with finite types for states and labels is also finitely branching. -/
instance Cslib.LTS.FinitelyBranching.of_finite [Finite State] [Finite Label] : lts.FinitelyBranching where
