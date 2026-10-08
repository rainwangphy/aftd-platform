import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSCat
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSWithIdle

/-!
# Cslib.LTS.Morphism

Topic: computability   Node: f11c8b342181

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Morphism`. Lean proof by Ayberk Tosun, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/LTSCat/Basic.lean (Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A morphism between two labelled transition systems consists of (1) a function on states, (2) a partial function on labels, and a proof that (1) preserves each transition along (2).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- A morphism between two labelled transition systems consists of (1) a function on states, (2) a partial function on labels, and a proof that (1) preserves each transition along (2). -/
structure Cslib.LTS.Morphism (lts₁ lts₂ : LTSCat) : Type where
  /-- Mapping of states of `lts₁` to states of `lts₂` -/
  stateMap : lts₁.State → lts₂.State
  /-- Mapping of labels of `lts₁` to labels of `lts₂` -/
  labelMap : lts₁.Label → Option lts₂.Label
  /-- Stipulation that `stateMap` preserve transitions -/
  labelMap_tr (s s' : lts₁.State) (l : lts₁.Label) :
    lts₁.lts.Tr s l s' → (withIdle lts₂.lts).Tr (stateMap s) (labelMap l) (stateMap s')
