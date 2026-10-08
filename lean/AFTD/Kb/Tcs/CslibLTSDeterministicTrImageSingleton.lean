import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSDeterministic
import AFTD.Kb.Tcs.CslibLTSImage

/-!
# Cslib.LTS.deterministic_tr_image_singleton

Topic: computability   Node: 735a744cd203

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.deterministic_tr_image_singleton`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.LTS.deterministic_tr_image_singleton
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
@[grind _=_]
theorem Cslib.LTS.deterministic_tr_image_singleton [lts.Deterministic] :
    lts.image s μ = {s'} ↔ lts.Tr s μ s' := by
  have := (lts.image s μ).eq_singleton_iff_unique_mem (a := s')
  grind
