import AFTD.Prelude
import AFTD.Kb.Tcs.Visited

/-!
# Visited.instZero

Topic: algorithms   Node: 4a7155c35f65

Provenance: formalization of a published result. Source: EconCSLib, `Visited.instZero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Visited.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Visited.instZero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
instance Visited.instZero : Zero (Visited A) := ⟨(∅ : Finset A)⟩
