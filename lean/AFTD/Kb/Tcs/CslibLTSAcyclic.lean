import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.RelationAcyclic
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr

/-!
# Cslib.LTS.Acyclic

Topic: computability   Node: 93e9ca3d6cc7

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Acyclic`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

An LTS is acyclic if its underlying unlabelled transition relation contains no nonempty cycle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An LTS is acyclic if its underlying unlabelled transition relation contains no nonempty cycle. -/
class Cslib.LTS.Acyclic (lts : LTS State Label) where
  [acyclic : Relation.Acyclic lts.UnlabelledTr]

attribute [instance] Cslib.LTS.Acyclic.acyclic
