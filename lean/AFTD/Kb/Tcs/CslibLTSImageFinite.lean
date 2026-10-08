import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSImage

/-!
# Cslib.LTS.ImageFinite

Topic: computability   Node: ab9a696c0cd4

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.ImageFinite`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An lts is image-finite if all images of its states are finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An lts is image-finite if all images of its states are finite. -/
abbrev Cslib.LTS.ImageFinite := ∀ s μ, Finite (lts.image s μ)
